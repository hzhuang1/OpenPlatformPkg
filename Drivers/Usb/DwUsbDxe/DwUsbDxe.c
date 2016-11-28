/** @file

  Copyright (c) 2015-2016, Linaro Limited. All rights reserved.

  This program and the accompanying materials
  are licensed and made available under the terms and conditions of the BSD License
  which accompanies this distribution.  The full text of the license may be found at
  http://opensource.org/licenses/bsd-license.php

  THE PROGRAM IS DISTRIBUTED UNDER THE BSD LICENSE ON AN "AS IS" BASIS,
  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.

**/

#include <IndustryStandard/Usb.h>
#include <Library/ArmLib.h>
#include <Library/BaseLib.h>
#include <Library/BaseMemoryLib.h>
#include <Library/CacheMaintenanceLib.h>
#include <Library/DebugLib.h>
#include <Library/IoLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/TimerLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiDriverEntryPoint.h>
#include <Library/UefiRuntimeServicesTableLib.h>
#include <Library/UncachedMemoryAllocationLib.h>
#include <Protocol/DwUsb.h>
#include <Protocol/UsbDevice.h>

#include "DwUsbDxe.h"

#define USB_TYPE_LENGTH              16
#define USB_BLOCK_HIGH_SPEED_SIZE    512
#define DATA_SIZE 32768
#define CMD_SIZE 512
#define MATCH_CMD_LITERAL(Cmd, Buf) !AsciiStrnCmp (Cmd, Buf, sizeof (Cmd) - 1)

// The time between interrupt polls, in units of 100 nanoseconds
// 10 Microseconds
#define DW_INTERRUPT_POLL_PERIOD 10000

EFI_GUID  gDwUsbProtocolGuid = DW_USB_PROTOCOL_GUID;

STATIC DWC_OTG_DEV_DMA_DESC     *gDmaDesc,*gDmaDescEp0,*gDmaDescIn;
STATIC USB_DEVICE_REQUEST       *pCtrlReq;
STATIC VOID                     *RxBuf;
STATIC UINTN                    RxDescBytes = 0;
STATIC UINTN                    mNumDataBytes;

STATIC DW_USB_PROTOCOL          *DwUsb;

STATIC USB_DEVICE_DESCRIPTOR    *mDeviceDescriptor;

// The config descriptor, interface descriptor, and endpoint descriptors in a
// buffer (in that order)
STATIC VOID                     *mDescriptors;
// Convenience pointers to those descriptors inside the buffer:
STATIC USB_INTERFACE_DESCRIPTOR *mInterfaceDescriptor;
STATIC USB_CONFIG_DESCRIPTOR    *mConfigDescriptor;
STATIC USB_ENDPOINT_DESCRIPTOR  *mEndpointDescriptors;

STATIC USB_DEVICE_RX_CALLBACK   mDataReceivedCallback;
STATIC USB_DEVICE_TX_CALLBACK   mDataSentCallback;

STATIC EFI_USB_STRING_DESCRIPTOR *mLangStringDescriptor;
STATIC EFI_USB_STRING_DESCRIPTOR *mManufacturerStringDescriptor;
STATIC EFI_USB_STRING_DESCRIPTOR *mProductStringDescriptor;
STATIC EFI_USB_STRING_DESCRIPTOR *mSerialStringDescriptor;

STATIC CHAR16 mLangString[] = { 0x409 };

STATIC CHAR16 mManufacturerString[] = {
  '9', '6', 'B', 'o', 'a', 'r', 'd', 's'
};

STATIC CHAR16 mProductString[] = {
  'H', 'i', 'K', 'e', 'y'
};

STATIC CHAR16 mSerialString[] = {
  '0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F'
};

/* To detect whether usb is running in high speed or full speed
 */
STATIC
UINT32
UsbDrvPortSpeed (
  VOID
  )
{
    /*
    * 2'b00: High speed (PHY clock is running at 30 or 60 MHz)
    */
    UINT32 Val;

    Val = MmioRead32 (DW_USB_BASE + DSTS) & DSTS_ENUMSPD_MASK;
    return Val == DSTS_ENUMSPD_HS;
}

STATIC
VOID
ResetEndpoints (
  VOID
  )
{
  /* EP0 IN ACTIVE NEXT=1 */
  MmioWrite32 (DW_USB_BASE + DIEPCTL0, DXEPCTL_USBACTEP | DXEPCTL_NEXTEP(1));

  /* EP0 OUT ACTIVE */
  MmioWrite32 (DW_USB_BASE + DOEPCTL0, DXEPCTL_USBACTEP);

  /* Clear any pending OTG Interrupts */
  MmioWrite32 (DW_USB_BASE + GOTGINT, ~0);

  /* Clear any pending interrupts */
  MmioWrite32 (DW_USB_BASE + GINTSTS, ~0);
  MmioWrite32 (DW_USB_BASE + DIEPINT0, ~0);
  MmioWrite32 (DW_USB_BASE + DOEPINT0, ~0);
  MmioWrite32 (DW_USB_BASE + DIEPINT1, ~0);
  MmioWrite32 (DW_USB_BASE + DOEPINT1, ~0);

  /* IN EP interrupt mask */
  MmioWrite32 (DW_USB_BASE + DIEPMSK,
               DIEPMSK_TIMEOUT | DXEPMSK_AHB_ERR | DXEPMSK_XFER_DONE);
  /* OUT EP interrupt mask */
  MmioWrite32 (DW_USB_BASE + DOEPMSK,
               DOEPMSK_SETUP | DXEPMSK_AHB_ERR | DXEPMSK_XFER_DONE);
  /* Enable interrupts on Ep0 */
  MmioWrite32 (DW_USB_BASE + DAINTMSK, DAINT_OUTEP(0) | DAINT_INEP(0));

  /* EP0 OUT Transfer Size:64 Bytes, 1 Packet, 3 Setup Packet, Read to receive setup packet*/
  MmioWrite32 (DW_USB_BASE + DOEPTSIZ0,
               DOEPTSIZ0_SUPCNT(3) | DOEPTSIZ0_PKTCNT | DOEPTSIZ0_XFERSIZE(64));

  //notes that:the compulsive conversion is expectable.
  gDmaDescEp0->status.b.bs = 0x3;
  gDmaDescEp0->status.b.mtrf = 0;
  gDmaDescEp0->status.b.sr = 0;
  gDmaDescEp0->status.b.l = 1;
  gDmaDescEp0->status.b.ioc = 1;
  gDmaDescEp0->status.b.sp = 0;
  gDmaDescEp0->status.b.bytes = 64;
  gDmaDescEp0->buf = (UINT32)(UINTN)(pCtrlReq);
  gDmaDescEp0->status.b.sts = 0;
  gDmaDescEp0->status.b.bs = 0x0;
  MmioWrite32 (DW_USB_BASE + DOEPDMA0, (UINT32)(UINTN)(gDmaDescEp0));
  /* EP0 OUT ENABLE CLEARNAK */
  MmioWrite32 (DW_USB_BASE + DOEPCTL0,
               (MmioRead32 (DW_USB_BASE + DOEPCTL0) | DXEPCTL_EPENA | DXEPCTL_CNAK));
}

STATIC
VOID
EpTx (
  IN UINT8 Ep,
  IN CONST VOID *Ptr,
  IN UINTN Len
  )
{
    UINT32 BlockSize;
    UINT32 Packets;

    /* EPx OUT ACTIVE */
    MmioWrite32 (DW_USB_BASE + DIEPCTL(Ep),
                 MmioRead32 (DW_USB_BASE + DIEPCTL(Ep)) | DXEPCTL_USBACTEP);
    if (!Ep) {
      BlockSize = 64;
    } else {
      BlockSize = UsbDrvPortSpeed() ? USB_BLOCK_HIGH_SPEED_SIZE : 64;
    }
    Packets = (Len + BlockSize - 1) / BlockSize;

    if (!Len) { //send a null packet
      /* one empty packet */
      gDmaDescIn->status.b.bs = 0x3;
      gDmaDescIn->status.b.l = 1;
      gDmaDescIn->status.b.ioc = 1;
      gDmaDescIn->status.b.sp = 1;
      gDmaDescIn->status.b.bytes = 0;
      gDmaDescIn->buf = 0;
      gDmaDescIn->status.b.sts = 0;
      gDmaDescIn->status.b.bs = 0x0;

      MmioWrite32 (DW_USB_BASE + DIEPDMA(Ep), (UINT32)(UINTN)(gDmaDescIn));             // DMA Address (DMAAddr) is zero
    } else { //prepare to send a packet
      MmioWrite32 (DW_USB_BASE + DIEPTSIZ(Ep), Len | (Packets << 19));
      
      //flush cache
      WriteBackDataCacheRange ((void*)Ptr, Len);
      
      gDmaDescIn->status.b.bs = 0x3;
      gDmaDescIn->status.b.l = 1;
      gDmaDescIn->status.b.ioc = 1;
      gDmaDescIn->status.b.sp = 1;
      gDmaDescIn->status.b.bytes = Len;
      gDmaDescIn->buf = (UINT32)((UINTN)Ptr);
      gDmaDescIn->status.b.sts = 0;
      gDmaDescIn->status.b.bs = 0x0;
      MmioWrite32 (DW_USB_BASE + DIEPDMA(Ep), (UINT32)(UINTN)(gDmaDescIn));         // Ptr is DMA address
    }
    ArmDataSynchronizationBarrier ();
    /* epena & cnak*/
    MmioWrite32 (DW_USB_BASE + DIEPCTL(Ep),
                 MmioRead32 (DW_USB_BASE + DIEPCTL(Ep)) | DXEPCTL_EPENA | DXEPCTL_CNAK);
    return;
}

STATIC
VOID
EpRx (
  IN UINT32 Ep,
  IN UINTN Len
  )
{
    /* EPx UNSTALL */
    MmioWrite32 (DW_USB_BASE + DOEPCTL(Ep),
                 MmioRead32 (DW_USB_BASE + DOEPCTL(Ep)) & ~DXEPCTL_STALL);
    /* EPx OUT ACTIVE */
    MmioWrite32 (DW_USB_BASE + DOEPCTL(Ep),
                 MmioRead32 (DW_USB_BASE + DOEPCTL(Ep)) | DXEPCTL_USBACTEP);

    if (Len >= DATA_SIZE)
	    RxDescBytes = DATA_SIZE;
    else
	    RxDescBytes = Len;

    RxBuf = AllocatePool (DATA_SIZE);
    ASSERT (RxBuf != NULL);

    InvalidateDataCacheRange (RxBuf, Len);

    gDmaDesc->status.b.bs = 0x3;
    gDmaDesc->status.b.mtrf = 0;
    gDmaDesc->status.b.sr = 0;
    gDmaDesc->status.b.l = 1;
    gDmaDesc->status.b.ioc = 1;
    gDmaDesc->status.b.sp = 0;
    gDmaDesc->status.b.bytes = (UINT32)RxDescBytes;
    gDmaDesc->buf = (UINT32)((UINTN)RxBuf);
    gDmaDesc->status.b.sts = 0;
    gDmaDesc->status.b.bs = 0x0;

    ArmDataSynchronizationBarrier ();
    MmioWrite32 (DW_USB_BASE + DOEPDMA(Ep), (UINT32)((UINTN)gDmaDesc));
    /* EPx OUT ENABLE CLEARNAK */
    MmioWrite32 (DW_USB_BASE + DOEPCTL(Ep),
                 MmioRead32 (DW_USB_BASE + DOEPCTL(Ep)) | DXEPCTL_EPENA | DXEPCTL_CNAK);
}

STATIC
EFI_STATUS
HandleGetDescriptor (
  IN USB_DEVICE_REQUEST  *Request
  )
{
  UINT8       DescriptorType;
  UINTN       ResponseSize;
  VOID       *ResponseData;

  ResponseSize = 0;
  ResponseData = NULL;

  // Pretty confused if bmRequestType is anything but this:
  ASSERT (Request->RequestType == USB_DEV_GET_DESCRIPTOR_REQ_TYPE);

  // Choose the response
  DescriptorType = Request->Value >> 8;
  switch (DescriptorType) {
  case USB_DESC_TYPE_DEVICE:
    DEBUG ((EFI_D_INFO, "USB: Got a request for device descriptor\n"));
    ResponseSize = sizeof (USB_DEVICE_DESCRIPTOR);
    ResponseData = mDeviceDescriptor;
    break;
  case USB_DESC_TYPE_CONFIG:
    DEBUG ((EFI_D_INFO, "USB: Got a request for config descriptor\n"));
    ResponseSize = mConfigDescriptor->TotalLength;
    ResponseData = mDescriptors;
    break;
  case USB_DESC_TYPE_STRING:
    DEBUG ((EFI_D_INFO, "USB: Got a request for String descriptor %d\n", Request->Value & 0xFF));
    switch (Request->Value & 0xff) {
    case 0:
      ResponseSize = mLangStringDescriptor->Length;
      ResponseData = mLangStringDescriptor;
      break;
    case 1:
      ResponseSize = mManufacturerStringDescriptor->Length;
      ResponseData = mManufacturerStringDescriptor;
      break;
    case 2:
      ResponseSize = mProductStringDescriptor->Length;
      ResponseData = mProductStringDescriptor;
      break;
    case 3:
      DwUsb->Get (mSerialStringDescriptor->String, &mSerialStringDescriptor->Length);
      ResponseSize = mSerialStringDescriptor->Length;
      ResponseData = mSerialStringDescriptor;
      break;
    }
    break;
  default:
    DEBUG ((EFI_D_INFO, "USB: Didn't understand request for descriptor 0x%04x\n", Request->Value));
    break;
  }

  // Send the response
  if (ResponseData) {
    ASSERT (ResponseSize != 0);

    if (Request->Length < ResponseSize) {
      // Truncate response
      ResponseSize = Request->Length;
    } else if (Request->Length > ResponseSize) {
      DEBUG ((EFI_D_INFO, "USB: Info: ResponseSize < wLength\n"));
    }

    EpTx(0, ResponseData, ResponseSize);
  }

  return EFI_SUCCESS;
}

STATIC
EFI_STATUS
HandleSetAddress (
  IN USB_DEVICE_REQUEST  *Request
  )
{
  // Pretty confused if bmRequestType is anything but this:
  ASSERT (Request->RequestType == USB_DEV_SET_ADDRESS_REQ_TYPE);
  DEBUG ((EFI_D_INFO, "USB: Setting address to %d\n", Request->Value));
  ResetEndpoints();

  MmioWrite32 (DW_USB_BASE + DCFG,
               (MmioRead32 (DW_USB_BASE + DCFG) & ~DCFG_DEVADDR_MASK) |
               (Request->Value << 4));
  EpTx(0, 0, 0);

  return EFI_SUCCESS;
}

STATIC
VOID
UsbDrvRequestEp (
  IN UINT32        type,
  IN UINT32        dir
  )
{
  UINT32 Ep = 1; /* always use EP1 */

  /*
   * (type << 18):Endpoint Type (EPType)
   * 0x10000000:Endpoint Enable (EPEna)
   * 0x000C000:Endpoint Type (EPType);Hardcoded to 00 for control.
   * (ep<<22):TxFIFO Number (TxFNum)
   * 0x20000:NAK Status (NAKSts);The core is transmitting NAK handshakes on this endpoint.
   */
  if (dir) {  // IN: to host
    MmioWrite32 (DW_USB_BASE + DIEPCTL(Ep),
                 (MmioRead32 (DW_USB_BASE + DIEPCTL(Ep)) & ~DXEPCTL_EPTYPE_MASK) |
                 DXEPCTL_EPTYPE(type) | (Ep << 22) | DXEPCTL_NAKSTS);
  } else {    // OUT: to device
    MmioWrite32 (DW_USB_BASE + DOEPCTL(Ep),
                 (MmioRead32 (DW_USB_BASE + DOEPCTL(Ep)) & ~DXEPCTL_EPTYPE_MASK) |
                 DXEPCTL_EPTYPE(type));
  }
}

STATIC
EFI_STATUS
HandleSetConfiguration (
  IN USB_DEVICE_REQUEST  *Request
  )
{
  ASSERT (Request->RequestType == USB_DEV_SET_CONFIGURATION_REQ_TYPE);

  // Cancel all transfers
  ResetEndpoints ();

  UsbDrvRequestEp (2, 0);
  UsbDrvRequestEp (2, 0x80);

  MmioWrite32 (DW_USB_BASE + DIEPCTL1,
               MmioRead32 (DW_USB_BASE + DIEPCTL1) | DXEPCTL_EPTYPE(2) |
               DXEPCTL_USBACTEP);

  /* Enable interrupts on all endpoints */
  MmioWrite32 (DW_USB_BASE + DAINTMSK, ~0);

  EpRx(1, CMD_SIZE);
  EpTx(0, 0, 0);
  return EFI_SUCCESS;
}


STATIC
EFI_STATUS
HandleDeviceRequest (
  IN USB_DEVICE_REQUEST  *Request
  )
{
  EFI_STATUS  Status;

  switch (Request->Request) {
  case USB_DEV_GET_DESCRIPTOR:
    Status = HandleGetDescriptor (Request);
    break;
  case USB_DEV_SET_ADDRESS:
    Status = HandleSetAddress (Request);
    break;
  case USB_DEV_SET_CONFIGURATION:
    Status = HandleSetConfiguration (Request);
    break;
  default:
    DEBUG ((EFI_D_ERROR,
      "Didn't understand RequestType 0x%x Request 0x%x\n",
      Request->RequestType, Request->Request));
      Status = EFI_INVALID_PARAMETER;
    break;
  }

  return Status;
}


// Instead of actually registering interrupt handlers, we poll the controller's
//  interrupt source register in this function.
STATIC
VOID
CheckInterrupts (
  IN EFI_EVENT  Event,
  IN VOID      *Context
  )
{
  UINT32 ints;
  UINT32 epints;
  UINT32        MaxPacketSize;

  ints = MmioRead32 (DW_USB_BASE + GINTSTS);
  /*
   * bus reset
   * The core sets this bit to indicate that a reset is detected on the USB.
   */
  if (ints & GINTSTS_USBRST) {
    MmioWrite32 (DW_USB_BASE + DCFG, DCFG_DESCDMA | DCFG_NZ_STS_OUT_HSHK);
    ResetEndpoints();
  }

  /*
   * enumeration done, we now know the speed
   * The core sets this bit to indicate that speed enumeration is complete. The
   * application must read the Device Status (DSTS) register to obtain the
   * enumerated speed.
   */
  if (ints & GINTSTS_ENUMDONE) {
    /* Set up the maximum packet sizes accordingly */
    MaxPacketSize = UsbDrvPortSpeed() ? USB_BLOCK_HIGH_SPEED_SIZE : 64;
    //Set Maximum In Packet Size (MPS)
    MmioWrite32 (DW_USB_BASE + DIEPCTL1,
                 (MmioRead32 (DW_USB_BASE + DIEPCTL1) & ~DXEPCTL_MPS_MASK) | MaxPacketSize);
    //Set Maximum Out Packet Size (MPS)
    MmioWrite32 (DW_USB_BASE + DOEPCTL1,
                 (MmioRead32 (DW_USB_BASE + DOEPCTL1) & ~DXEPCTL_MPS_MASK) | MaxPacketSize);
  }

  /*
   * IN EP event
   * The core sets this bit to indicate that an interrupt is pending on one of the IN
   * endpoints of the core (in Device mode). The application must read the
   * Device All Endpoints Interrupt (DAINT) register to determine the exact
   * number of the IN endpoint on which the interrupt occurred, and then read
   * the corresponding Device IN Endpoint-n Interrupt (DIEPINTn) register to
   * determine the exact cause of the interrupt. The application must clear the
   * appropriate status bit in the corresponding DIEPINTn register to clear this bit.
   */
  if (ints & GINTSTS_IEPINT) {
    epints = MmioRead32 (DW_USB_BASE + DIEPINT0);
    MmioWrite32 (DW_USB_BASE + DIEPINT0, epints);
    if (epints & DXEPINT_XFERCOMPL) {
      /* Transfer Completed Interrupt (XferCompl) */
      DEBUG ((EFI_D_INFO, "INT: IN TX completed.DIEPTSIZ(0) = 0x%x.\n",
              MmioRead32 (DW_USB_BASE + DIEPTSIZ0)));
    }
   
    epints = MmioRead32 (DW_USB_BASE + DIEPINT1);
    MmioWrite32 (DW_USB_BASE + DIEPINT1, epints);
    if (epints & DXEPINT_XFERCOMPL) {
      DEBUG ((EFI_D_INFO, "ep1: IN TX completed\n"));
    }
  }

  /*
   * OUT EP event
   * The core sets this bit to indicate that an interrupt is pending on one of the
   * OUT endpoints of the core (in Device mode). The application must read the
   * Device All Endpoints Interrupt (DAINT) register to determine the exact
   * number of the OUT endpoint on which the interrupt occurred, and then read
   * the corresponding Device OUT Endpoint-n Interrupt (DOEPINTn) register
   * to determine the exact cause of the interrupt. The application must clear the
   * appropriate status bit in the corresponding DOEPINTn register to clear this bit.
   */
  if (ints & GINTSTS_OEPINT) {
    /* indicates the status of an endpoint
     * with respect to USB- and AHB-related events. */
    epints = MmioRead32 (DW_USB_BASE + DOEPINT0);
    if (epints) {
      MmioWrite32 (DW_USB_BASE + DOEPINT0, epints);

      if (epints & DXEPINT_XFERCOMPL) {
        DEBUG ((EFI_D_INFO, "INT: EP0 RX completed. DOEPTSIZ(0) = 0x%x.\n",
                MmioRead32 (DW_USB_BASE + DOEPTSIZ0)));
      } /* EP0: DXEPINT_XFERCOMPL */
      /*
       * IN Token Received When TxFIFO is Empty (INTknTXFEmp)
       * Indicates that an IN token was received when the associated TxFIFO (periodic/nonperiodic)
       * was empty. This interrupt is asserted on the endpoint for which the IN token
       * was received.
       */
      if (epints & DXEPINT_SETUP) { /* SETUP phase done */
        MmioWrite32 (DW_USB_BASE + DIEPCTL0,
                     MmioRead32 (DW_USB_BASE + DIEPCTL0) | DXEPCTL_SNAK);
        MmioWrite32 (DW_USB_BASE + DOEPCTL0,
                     MmioRead32 (DW_USB_BASE + DOEPCTL0) | DXEPCTL_SNAK);
        MmioWrite32 (DW_USB_BASE + DIEPINT0, ~0); /* clear IN EP interrupts */
        HandleDeviceRequest ((USB_DEVICE_REQUEST *)pCtrlReq);
      } /* EP0: DXEPINT_SETUP */
    
      /* Make sure EP0 OUT is set up to accept the next request */
      /* memset(pCtrlReq, 0, NUM_ENDPOINTS*8); */
      MmioWrite32 (DW_USB_BASE + DOEPTSIZ0,
                   DOEPTSIZ0_SUPCNT(3) | DOEPTSIZ0_PKTCNT | DOEPTSIZ0_XFERSIZE(64));
      /*
       * IN Token Received When TxFIFO is Empty (INTknTXFEmp)
       * Indicates that an IN token was received when the associated TxFIFO (periodic/nonperiodic)
       * was empty. This interrupt is asserted on the endpoint for which the IN token
       * was received.
       */
      gDmaDescEp0->status.b.bs = 0x3;
      gDmaDescEp0->status.b.mtrf = 0;
      gDmaDescEp0->status.b.sr = 0;
      gDmaDescEp0->status.b.l = 1;
      gDmaDescEp0->status.b.ioc = 1;
      gDmaDescEp0->status.b.sp = 0;
      gDmaDescEp0->status.b.bytes = 64;
      gDmaDescEp0->buf = (UINT32)(UINTN)(pCtrlReq);
      gDmaDescEp0->status.b.sts = 0;
      gDmaDescEp0->status.b.bs = 0x0;
      MmioWrite32 (DW_USB_BASE + DOEPDMA0, (UINT32)(UINTN)(gDmaDescEp0));
      // endpoint enable; clear NAK
      MmioWrite32 (DW_USB_BASE + DOEPCTL0, DXEPCTL_EPENA | DXEPCTL_CNAK);
    } /* EP0: epints */

    epints = (MmioRead32 (DW_USB_BASE + DOEPINT1));
    if (epints) {
      MmioWrite32 (DW_USB_BASE + DOEPINT1, epints);
      if (epints & DXEPINT_XFERCOMPL) {
        UINTN bytes = RxDescBytes - gDmaDesc->status.b.bytes;
        UINTN Len = 0;
      
        ArmDataSynchronizationBarrier ();

        if (MATCH_CMD_LITERAL ("download", RxBuf)) {
      	  mNumDataBytes = AsciiStrHexToUint64 (RxBuf + sizeof ("download"));
        } else {
      	if (mNumDataBytes != 0)
      		mNumDataBytes -= bytes;
        } /* download */
      
        mDataReceivedCallback (bytes, RxBuf);
      
        if (mNumDataBytes == 0) {
      	  Len = CMD_SIZE;
        } else if (mNumDataBytes > DATA_SIZE) {
      	  Len = DATA_SIZE;
        } else {
      	  Len = mNumDataBytes;
        } /* mNumDataBytes */
      
        EpRx(1, Len);
      } /* EP1: DXEPINT_XFERCOMPL */
    } /* EP1: epints */
  } /* OEPINT */

  /* Write to clear interrupts */
  MmioWrite32 (DW_USB_BASE + GINTSTS, ints);
}

EFI_STATUS
DwUsbSend (
  IN        UINT8  EndpointIndex,
  IN        UINTN  Size,
  IN  CONST VOID  *Buffer
  )
{
    EpTx(EndpointIndex, Buffer, Size);
    return 0;
}

STATIC
VOID
DwUsbInit (
  VOID
  )
{
  VOID     *buf;
  UINT32   data;

  buf = UncachedAllocatePages (16);
  gDmaDesc = buf;
  gDmaDescEp0 = gDmaDesc + sizeof(DWC_OTG_DEV_DMA_DESC);
  gDmaDescIn = gDmaDescEp0 + sizeof(DWC_OTG_DEV_DMA_DESC);
  pCtrlReq = (USB_DEVICE_REQUEST *)gDmaDescIn + sizeof(DWC_OTG_DEV_DMA_DESC);

  SetMem(gDmaDesc, sizeof(DWC_OTG_DEV_DMA_DESC), 0);
  SetMem(gDmaDescEp0, sizeof(DWC_OTG_DEV_DMA_DESC), 0);
  SetMem(gDmaDescIn, sizeof(DWC_OTG_DEV_DMA_DESC), 0);

  /*Reset usb controller.*/
  /* Wait for OTG AHB master idle */
  do {
    data = MmioRead32 (DW_USB_BASE + GRSTCTL) & GRSTCTL_AHBIDLE;
  } while (data == 0);

  /* OTG: Assert Software Reset */
  MmioWrite32 (DW_USB_BASE + GRSTCTL, GRSTCTL_CSFTRST);

  /* Wait for OTG to ack reset */
  while (MmioRead32 (DW_USB_BASE + GRSTCTL) & GRSTCTL_CSFTRST);

  /* Wait for OTG AHB master idle */
  while ((MmioRead32 (DW_USB_BASE + GRSTCTL) & GRSTCTL_AHBIDLE) == 0);

  MmioWrite32 (DW_USB_BASE + GDFIFOCFG, DATA_FIFO_CONFIG);
  MmioWrite32 (DW_USB_BASE + GRXFSIZ, RX_SIZE);
  MmioWrite32 (DW_USB_BASE + GNPTXFSIZ, ENDPOINT_TX_SIZE);
  MmioWrite32 (DW_USB_BASE + DIEPTXF1, DATA_IN_ENDPOINT_TX_FIFO1);
  MmioWrite32 (DW_USB_BASE + DIEPTXF2, DATA_IN_ENDPOINT_TX_FIFO2);
  MmioWrite32 (DW_USB_BASE + DIEPTXF3, DATA_IN_ENDPOINT_TX_FIFO3);
  MmioWrite32 (DW_USB_BASE + DIEPTXF4, DATA_IN_ENDPOINT_TX_FIFO4);
  MmioWrite32 (DW_USB_BASE + DIEPTXF5, DATA_IN_ENDPOINT_TX_FIFO5);
  MmioWrite32 (DW_USB_BASE + DIEPTXF6, DATA_IN_ENDPOINT_TX_FIFO6);
  MmioWrite32 (DW_USB_BASE + DIEPTXF7, DATA_IN_ENDPOINT_TX_FIFO7);
  MmioWrite32 (DW_USB_BASE + DIEPTXF8, DATA_IN_ENDPOINT_TX_FIFO8);
  MmioWrite32 (DW_USB_BASE + DIEPTXF9, DATA_IN_ENDPOINT_TX_FIFO9);
  MmioWrite32 (DW_USB_BASE + DIEPTXF10, DATA_IN_ENDPOINT_TX_FIFO10);
  MmioWrite32 (DW_USB_BASE + DIEPTXF11, DATA_IN_ENDPOINT_TX_FIFO11);
  MmioWrite32 (DW_USB_BASE + DIEPTXF12, DATA_IN_ENDPOINT_TX_FIFO12);
  MmioWrite32 (DW_USB_BASE + DIEPTXF13, DATA_IN_ENDPOINT_TX_FIFO13);
  MmioWrite32 (DW_USB_BASE + DIEPTXF14, DATA_IN_ENDPOINT_TX_FIFO14);
  MmioWrite32 (DW_USB_BASE + DIEPTXF15, DATA_IN_ENDPOINT_TX_FIFO15);

  /*
   * set Periodic TxFIFO Empty Level,
   * Non-Periodic TxFIFO Empty Level,
   * Enable DMA, Unmask Global Intr
   */
  MmioWrite32 (DW_USB_BASE + GAHBCFG, GAHBCFG_CTRL_MASK);

  /* select 8bit UTMI+, ULPI Inerface */
  MmioWrite32 (DW_USB_BASE + GUSBCFG, GUSBCFG_PHY_8BIT);

  /* Detect usb work mode,host or device? */
  do {
    data = MmioRead32 (DW_USB_BASE + GINTSTS);
  } while (data & GINTSTS_CURMODE_HOST);
  MicroSecondDelay(3);

  /*Init global and device mode csr register.*/
  /*set Non-Zero-Length status out handshake */
  data = (0x20 << DCFG_EPMISCNT_SHIFT) | DCFG_NZ_STS_OUT_HSHK;
  MmioWrite32 (DW_USB_BASE + DCFG, data);

  /* Interrupt unmask: IN event, OUT event, bus reset */
  data = GINTSTS_OEPINT | GINTSTS_IEPINT | GINTSTS_ENUMDONE | GINTSTS_USBRST;
  MmioWrite32 (DW_USB_BASE + GINTMSK, data);

  do {
    data = MmioRead32 (DW_USB_BASE + GINTSTS) & GINTSTS_ENUMDONE;
  } while (data);

  /* Clear any pending OTG Interrupts */
  MmioWrite32 (DW_USB_BASE + GOTGINT, ~0);
  /* Clear any pending interrupts */
  MmioWrite32 (DW_USB_BASE + GINTSTS, ~0);
  MmioWrite32 (DW_USB_BASE + GINTMSK, ~0);
  data = MmioRead32 (DW_USB_BASE + GOTGINT);
  data &= ~0x3000;
  MmioWrite32 (DW_USB_BASE + GOTGINT, data);

  /*endpoint settings cfg*/
  ResetEndpoints();
  MicroSecondDelay (1);

  /*init finish. and ready to transfer data*/

  /* Soft Disconnect */
  MmioWrite32 (DW_USB_BASE + DCTL, DCTL_PWRONPRGDONE | DCTL_SFTDISCON);
  MicroSecondDelay(10000);

  /* Soft Reconnect */
  MmioWrite32 (DW_USB_BASE + DCTL, DCTL_PWRONPRGDONE);
}

EFI_STATUS
EFIAPI
DwUsbStart (
  IN USB_DEVICE_DESCRIPTOR   *DeviceDescriptor,
  IN VOID                   **Descriptors,
  IN USB_DEVICE_RX_CALLBACK   RxCallback,
  IN USB_DEVICE_TX_CALLBACK   TxCallback
  )
{
  UINT8                    *Ptr;
  EFI_STATUS                Status;
  EFI_EVENT                 TimerEvent;
  UINTN                     StringDescriptorSize;

  ASSERT (DeviceDescriptor != NULL);
  ASSERT (Descriptors[0] != NULL);
  ASSERT (RxCallback != NULL);
  ASSERT (TxCallback != NULL);

  StringDescriptorSize = sizeof (EFI_USB_STRING_DESCRIPTOR) +
	                 sizeof (mLangString) + 1;
  mLangStringDescriptor = AllocateZeroPool (StringDescriptorSize);
  ASSERT (mLangStringDescriptor != NULL);
  mLangStringDescriptor->Length = sizeof (mLangString);
  mLangStringDescriptor->DescriptorType = USB_DESC_TYPE_STRING;
  CopyMem (mLangStringDescriptor->String, mLangString,
	   mLangStringDescriptor->Length);

  StringDescriptorSize = sizeof (EFI_USB_STRING_DESCRIPTOR) +
	                 sizeof (mManufacturerString) + 1;
  mManufacturerStringDescriptor = AllocateZeroPool (StringDescriptorSize);
  ASSERT (mManufacturerStringDescriptor != NULL);
  mManufacturerStringDescriptor->Length = sizeof (mManufacturerString);
  mManufacturerStringDescriptor->DescriptorType = USB_DESC_TYPE_STRING;
  CopyMem (mManufacturerStringDescriptor->String, mManufacturerString,
	   mManufacturerStringDescriptor->Length);

  StringDescriptorSize = sizeof (EFI_USB_STRING_DESCRIPTOR) +
	                 sizeof (mProductString) + 1;
  mProductStringDescriptor = AllocateZeroPool (StringDescriptorSize);
  ASSERT (mProductStringDescriptor != NULL);
  mProductStringDescriptor->Length = sizeof (mProductString);
  mProductStringDescriptor->DescriptorType = USB_DESC_TYPE_STRING;
  CopyMem (mProductStringDescriptor->String, mProductString,
	   mProductStringDescriptor->Length);

  StringDescriptorSize = sizeof (EFI_USB_STRING_DESCRIPTOR) +
	                 sizeof (mSerialString) + 1;
  mSerialStringDescriptor = AllocateZeroPool (StringDescriptorSize);
  ASSERT (mSerialStringDescriptor != NULL);
  mSerialStringDescriptor->Length = sizeof (mSerialString);
  mSerialStringDescriptor->DescriptorType = USB_DESC_TYPE_STRING;
  CopyMem (mSerialStringDescriptor->String, mSerialString,
	   mSerialStringDescriptor->Length);

  DwUsbInit();

  mDeviceDescriptor = DeviceDescriptor;
  mDescriptors = Descriptors[0];

  // Right now we just support one configuration
  ASSERT (mDeviceDescriptor->NumConfigurations == 1);
  mDeviceDescriptor->StrManufacturer = 1;
  mDeviceDescriptor->StrProduct = 2;
  mDeviceDescriptor->StrSerialNumber = 3;
  // ... and one interface
  mConfigDescriptor = (USB_CONFIG_DESCRIPTOR *)mDescriptors;
  ASSERT (mConfigDescriptor->NumInterfaces == 1);

  Ptr = ((UINT8 *) mDescriptors) + sizeof (USB_CONFIG_DESCRIPTOR);
  mInterfaceDescriptor = (USB_INTERFACE_DESCRIPTOR *) Ptr;
  Ptr += sizeof (USB_INTERFACE_DESCRIPTOR);

  mEndpointDescriptors = (USB_ENDPOINT_DESCRIPTOR *) Ptr;

  mDataReceivedCallback = RxCallback;
  mDataSentCallback = TxCallback;

  // Register a timer event so CheckInterupts gets called periodically
  Status = gBS->CreateEvent (
                  EVT_TIMER | EVT_NOTIFY_SIGNAL,
                  TPL_CALLBACK,
                  CheckInterrupts,
                  NULL,
                  &TimerEvent
                  );
  ASSERT_EFI_ERROR (Status);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  Status = gBS->SetTimer (
                  TimerEvent,
                  TimerPeriodic,
                  DW_INTERRUPT_POLL_PERIOD
                  );
  ASSERT_EFI_ERROR (Status);

  return Status;
}

USB_DEVICE_PROTOCOL mUsbDevice = {
  DwUsbStart,
  DwUsbSend
};


EFI_STATUS
EFIAPI
DwUsbEntryPoint (
  IN EFI_HANDLE                            ImageHandle,
  IN EFI_SYSTEM_TABLE                      *SystemTable
  )
{
  EFI_STATUS      Status;
  UINT8           UsbMode;

  Status = gBS->LocateProtocol (&gDwUsbProtocolGuid, NULL, (VOID **) &DwUsb);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  //Mode: 1 for device, 0 for Host
  UsbMode = USB_DEVICE_MODE;
  Status = DwUsb->PhyInit(UsbMode);
  if (EFI_ERROR (Status)) {
    return Status;
  }

  return gBS->InstallProtocolInterface (
		  &ImageHandle,
		  &gUsbDeviceProtocolGuid,
		  EFI_NATIVE_INTERFACE,
		  &mUsbDevice
		  );
}
