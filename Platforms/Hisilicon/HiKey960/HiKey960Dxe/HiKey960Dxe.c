/** @file
*
*  Copyright (c) 2016, Linaro Ltd. All rights reserved.
*
*  This program and the accompanying materials
*  are licensed and made available under the terms and conditions of the BSD License
*  which accompanies this distribution.  The full text of the license may be found at
*  http://opensource.org/licenses/bsd-license.php
*
*  THE PROGRAM IS DISTRIBUTED UNDER THE BSD LICENSE ON AN "AS IS" BASIS,
*  WITHOUT WARRANTIES OR REPRESENTATIONS OF ANY KIND, EITHER EXPRESS OR IMPLIED.
*
**/

#include <Guid/EventGroup.h>

#include <Hi3660.h>

#include <Library/BaseMemoryLib.h>
#include <Library/MemoryAllocationLib.h>
#include <Library/IoLib.h>
#include <Library/PrintLib.h>
#include <Library/TimerLib.h>
#include <Library/UefiBootServicesTableLib.h>
#include <Library/UefiRuntimeServicesTableLib.h>

STATIC
VOID
InitUfs (
  VOID
  )
{
  UINT32       Data, Mask;
  
  MmioWrite32 (CRG_REG_BASE + CRG_PERRSTEN3_OFFSET, PERI_UFS_BIT);
  do {
    Data = MmioRead32 (CRG_REG_BASE + CRG_PERRSTSTAT3_OFFSET);
  } while ((Data & PERI_UFS_BIT) == 0);
  MicroSecondDelay (1);
  
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_PSW_POWER_CTRL_OFFSET);
  Data |= BIT_UFS_PSW_MTCMOS_EN;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_PSW_POWER_CTRL_OFFSET, Data);
  MicroSecondDelay (1);
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_HC_LP_CTRL_OFFSET);
  Data |= BIT_SYSCTRL_PWR_READY;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_HC_LP_CTRL_OFFSET, Data);
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_UFS_DEVICE_RESET_CTRL_OFFSET,
               MASK_UFS_DEVICE_RESET);
  Mask = SC_DIV_UFS_PERIBUS << 16;
  MmioWrite32 (CRG_REG_BASE + CRG_CLKDIV17_OFFSET, Mask);
  Mask = SC_DIV_UFSPHY_CFG_MASK << 16;
  Data = SC_DIV_UFSPHY_CFG(3);
  MmioWrite32 (CRG_REG_BASE + CRG_CLKDIV16_OFFSET, Mask | Data);
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_CLK_CTRL_OFFSET);
  Data &= ~MASK_SYSCTRL_CFG_CLOCK_FREQ;
  Data |= 0x39;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_CLK_CTRL_OFFSET, Data);

  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_CLK_CTRL_OFFSET);
  Data &= ~MASK_SYSCTRL_REF_CLOCK_SEL;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_CLK_CTRL_OFFSET, Data);
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_CLK_CTRL_OFFSET);
  Data |= BIT_SYSCTRL_PSW_CLK_EN;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_CLK_CTRL_OFFSET, Data);
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_PSW_POWER_CTRL_OFFSET);
  Data &= ~BIT_UFS_PSW_ISO_CTRL;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_PSW_POWER_CTRL_OFFSET, Data);
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_ISO_EN_OFFSET);
  Data &= ~BIT_UFS_PHY_ISO_CTRL;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_PHY_ISO_EN_OFFSET, Data);
  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_HC_LP_CTRL_OFFSET);
  Data &= ~BIT_SYSCTRL_LP_ISOL_EN;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_HC_LP_CTRL_OFFSET, Data);
  MmioWrite32 (CRG_REG_BASE + CRG_PERRSTDIS3_OFFSET, PERI_ARST_UFS_BIT);

  Data = MmioRead32 (UFS_SYS_REG_BASE + UFS_SYS_RESET_CTRL_EN_OFFSET);
  Data |= BIT_SYSCTRL_LP_RESET_N;
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_RESET_CTRL_EN_OFFSET, Data);
  MicroSecondDelay (1);
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_UFS_DEVICE_RESET_CTRL_OFFSET,
               MASK_UFS_DEVICE_RESET | BIT_UFS_DEVICE_RESET);
  MicroSecondDelay (20);
  MmioWrite32 (UFS_SYS_REG_BASE + UFS_SYS_UFS_DEVICE_RESET_CTRL_OFFSET,
               0x03300330);

  MmioWrite32 (CRG_REG_BASE + CRG_PERRSTDIS3_OFFSET, PERI_UFS_BIT);
  do {
    Data = MmioRead32 (CRG_REG_BASE + CRG_PERRSTSTAT3_OFFSET);
  } while (Data & PERI_UFS_BIT);
}


/**
  Notification function of the event defined as belonging to the
  EFI_END_OF_DXE_EVENT_GROUP_GUID event group that was created in
  the entry point of the driver.

  This function is called when an event belonging to the
  EFI_END_OF_DXE_EVENT_GROUP_GUID event group is signalled. Such an
  event is signalled once at the end of the dispatching of all
  drivers (end of the so called DXE phase).

  @param[in]  Event    Event declared in the entry point of the driver whose
                       notification function is being invoked.
  @param[in]  Context  NULL
**/
STATIC
VOID
OnEndOfDxe (
  IN EFI_EVENT  Event,
  IN VOID       *Context
  )
{
}

EFI_STATUS
EFIAPI
HiKey960EntryPoint (
  IN EFI_HANDLE         ImageHandle,
  IN EFI_SYSTEM_TABLE   *SystemTable
  )
{
  EFI_STATUS            Status;
  EFI_EVENT             EndOfDxeEvent;

  InitUfs ();

  //
  // Create an event belonging to the "gEfiEndOfDxeEventGroupGuid" group.
  // The "OnEndOfDxe()" function is declared as the call back function.
  // It will be called at the end of the DXE phase when an event of the
  // same group is signalled to inform about the end of the DXE phase.
  // Install the INSTALL_FDT_PROTOCOL protocol.
  //
  Status = gBS->CreateEventEx (
                  EVT_NOTIFY_SIGNAL,
                  TPL_CALLBACK,
                  OnEndOfDxe,
                  NULL,
                  &gEfiEndOfDxeEventGroupGuid,
                  &EndOfDxeEvent
                  );

  return Status;
}
