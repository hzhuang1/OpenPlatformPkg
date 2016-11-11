/** @file
*
*  Copyright (c) 2016, Linaro Limited. All rights reserved.
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

#include <Library/ArmPlatformLib.h>
#include <Library/DebugLib.h>
#include <Library/HobLib.h>
#include <Library/PcdLib.h>
#include <Library/IoLib.h>
#include <Library/MemoryAllocationLib.h>

// The total number of descriptors, including the final "end-of-table" descriptor.
#define MAX_VIRTUAL_MEMORY_MAP_DESCRIPTORS 12

// DDR attributes
#define DDR_ATTRIBUTES_CACHED           ARM_MEMORY_REGION_ATTRIBUTE_WRITE_BACK
#define DDR_ATTRIBUTES_UNCACHED         ARM_MEMORY_REGION_ATTRIBUTE_UNCACHED_UNBUFFERED

#define HI3660_PERIPH_BASE              0xE0000000
#define HI3660_PERIPH_SZ                0x20000000

#define HIKEY960_EXTRA1_SYSTEM_MEMORY_BASE  0x11000000
#define HIKEY960_EXTRA1_SYSTEM_MEMORY_SIZE  0xDF000000
#define HIKEY960_EXTRA2_SYSTEM_MEMORY_BASE  0x0000000100000000
#define HIKEY960_EXTRA2_SYSTEM_MEMORY_SIZE  0x0000000020000000

#define HIKEY960_MEMORY_SIZE                0x0000000100000000

STATIC struct HiKeyReservedMemory {
  EFI_PHYSICAL_ADDRESS         Offset;
  EFI_PHYSICAL_ADDRESS         Size;
} HiKeyReservedMemoryBuffer [] = {
  { 0x21F00000, 0x00100000 },    // PSTORE/RAMOOPS
  { 0x3E000000, 0x02000000 }     // TEE OS
};

/**
  Return the Virtual Memory Map of your platform

  This Virtual Memory Map is used by MemoryInitPei Module to initialize the MMU on your platform.

  @param[out]   VirtualMemoryMap    Array of ARM_MEMORY_REGION_DESCRIPTOR describing a Physical-to-
                                    Virtual Memory mapping. This array must be ended by a zero-filled
                                    entry

**/
VOID
ArmPlatformGetVirtualMemoryMap (
  IN ARM_MEMORY_REGION_DESCRIPTOR** VirtualMemoryMap
  )
{
  ARM_MEMORY_REGION_ATTRIBUTES  CacheAttributes;
  UINTN                         Index = 0, Count, ReservedTop;
  ARM_MEMORY_REGION_DESCRIPTOR  *VirtualMemoryTable;
  EFI_PEI_HOB_POINTERS          NextHob;
  EFI_RESOURCE_ATTRIBUTE_TYPE   ResourceAttributes;
  UINT64                        ResourceLength;
  EFI_PHYSICAL_ADDRESS          ResourceTop;

  ResourceAttributes = (
      EFI_RESOURCE_ATTRIBUTE_PRESENT |
      EFI_RESOURCE_ATTRIBUTE_INITIALIZED |
      EFI_RESOURCE_ATTRIBUTE_UNCACHEABLE |
      EFI_RESOURCE_ATTRIBUTE_WRITE_COMBINEABLE |
      EFI_RESOURCE_ATTRIBUTE_WRITE_THROUGH_CACHEABLE |
      EFI_RESOURCE_ATTRIBUTE_WRITE_BACK_CACHEABLE |
      EFI_RESOURCE_ATTRIBUTE_TESTED
  );

  // Create initial Base Hob for system memory.
  BuildResourceDescriptorHob (
      EFI_RESOURCE_SYSTEM_MEMORY,
      ResourceAttributes,
      PcdGet64 (PcdSystemMemoryBase),
      PcdGet64 (PcdSystemMemorySize)
  );

  NextHob.Raw = GetHobList ();
  Count = sizeof (HiKeyReservedMemoryBuffer) / sizeof (struct HiKeyReservedMemory);
  while ((NextHob.Raw = GetNextHob (EFI_HOB_TYPE_RESOURCE_DESCRIPTOR, NextHob.Raw)) != NULL)
  {
    if (Index >= Count)
      break;
    if ((NextHob.ResourceDescriptor->ResourceType == EFI_RESOURCE_SYSTEM_MEMORY) &&
        (HiKeyReservedMemoryBuffer[Index].Offset >= NextHob.ResourceDescriptor->PhysicalStart) &&
        ((HiKeyReservedMemoryBuffer[Index].Offset + HiKeyReservedMemoryBuffer[Index].Size) <=
         NextHob.ResourceDescriptor->PhysicalStart + NextHob.ResourceDescriptor->ResourceLength))
    {
      ResourceAttributes = NextHob.ResourceDescriptor->ResourceAttribute;
      ResourceLength = NextHob.ResourceDescriptor->ResourceLength;
      ResourceTop = NextHob.ResourceDescriptor->PhysicalStart + ResourceLength;
      ReservedTop = HiKeyReservedMemoryBuffer[Index].Offset + HiKeyReservedMemoryBuffer[Index].Size;

      // Create the System Memory HOB for the reserved buffer
      BuildResourceDescriptorHob (EFI_RESOURCE_MEMORY_RESERVED,
                                  EFI_RESOURCE_ATTRIBUTE_PRESENT,
                                  HiKeyReservedMemoryBuffer[Index].Offset,
                                  HiKeyReservedMemoryBuffer[Index].Size);
      // Update the HOB
      NextHob.ResourceDescriptor->ResourceLength = HiKeyReservedMemoryBuffer[Index].Offset - NextHob.ResourceDescriptor->PhysicalStart;

      // If there is some memory available on the top of the reserved memory then create a HOB
      if (ReservedTop < ResourceTop)
      {
        BuildResourceDescriptorHob (EFI_RESOURCE_SYSTEM_MEMORY,
                                    ResourceAttributes,
                                    ReservedTop,
                                    ResourceTop - ReservedTop);
      }
      Index++;
    }
    NextHob.Raw = GET_NEXT_HOB (NextHob);
  }

  // Declared the additional memory
  ResourceAttributes =
      EFI_RESOURCE_ATTRIBUTE_PRESENT |
      EFI_RESOURCE_ATTRIBUTE_INITIALIZED |
      EFI_RESOURCE_ATTRIBUTE_UNCACHEABLE |
      EFI_RESOURCE_ATTRIBUTE_WRITE_COMBINEABLE |
      EFI_RESOURCE_ATTRIBUTE_WRITE_THROUGH_CACHEABLE |
      EFI_RESOURCE_ATTRIBUTE_WRITE_BACK_CACHEABLE |
      EFI_RESOURCE_ATTRIBUTE_TESTED;

  BuildResourceDescriptorHob (
    EFI_RESOURCE_SYSTEM_MEMORY,
    ResourceAttributes,
    HIKEY960_EXTRA1_SYSTEM_MEMORY_BASE,
    HIKEY960_EXTRA1_SYSTEM_MEMORY_SIZE);

  BuildResourceDescriptorHob (
    EFI_RESOURCE_SYSTEM_MEMORY,
    ResourceAttributes,
    HIKEY960_EXTRA2_SYSTEM_MEMORY_BASE,
    HIKEY960_EXTRA2_SYSTEM_MEMORY_SIZE);

  ASSERT (VirtualMemoryMap != NULL);

  VirtualMemoryTable = (ARM_MEMORY_REGION_DESCRIPTOR*)AllocatePages(EFI_SIZE_TO_PAGES (sizeof(ARM_MEMORY_REGION_DESCRIPTOR) * MAX_VIRTUAL_MEMORY_MAP_DESCRIPTORS));
  if (VirtualMemoryTable == NULL) {
      return;
  }

  if (FeaturePcdGet(PcdCacheEnable) == TRUE) {
      CacheAttributes = DDR_ATTRIBUTES_CACHED;
  } else {
      CacheAttributes = DDR_ATTRIBUTES_UNCACHED;
  }

  Index = 0;

  // Hi3660 SOC peripherals
  VirtualMemoryTable[Index].PhysicalBase    = HI3660_PERIPH_BASE;
  VirtualMemoryTable[Index].VirtualBase     = HI3660_PERIPH_BASE;
  VirtualMemoryTable[Index].Length          = HI3660_PERIPH_SZ;
  VirtualMemoryTable[Index].Attributes      = ARM_MEMORY_REGION_ATTRIBUTE_DEVICE;

  // DDR - the first 256MB section
  VirtualMemoryTable[++Index].PhysicalBase  = PcdGet64 (PcdSystemMemoryBase);
  VirtualMemoryTable[Index].VirtualBase     = PcdGet64 (PcdSystemMemoryBase);
  VirtualMemoryTable[Index].Length          = PcdGet64 (PcdSystemMemorySize);
  VirtualMemoryTable[Index].Attributes      = CacheAttributes;

  // DDR - the second section for the rest of 3.5GB
  VirtualMemoryTable[++Index].PhysicalBase = HIKEY960_EXTRA1_SYSTEM_MEMORY_BASE;
  VirtualMemoryTable[Index].VirtualBase    = HIKEY960_EXTRA1_SYSTEM_MEMORY_BASE;
  VirtualMemoryTable[Index].Length         = HIKEY960_EXTRA1_SYSTEM_MEMORY_SIZE;
  VirtualMemoryTable[Index].Attributes     = CacheAttributes;

  // DDR - the third 0.5GB section
  VirtualMemoryTable[++Index].PhysicalBase = HIKEY960_EXTRA2_SYSTEM_MEMORY_BASE;
  VirtualMemoryTable[Index].VirtualBase    = HIKEY960_EXTRA2_SYSTEM_MEMORY_BASE;
  VirtualMemoryTable[Index].Length         = HIKEY960_EXTRA2_SYSTEM_MEMORY_SIZE;
  VirtualMemoryTable[Index].Attributes     = CacheAttributes;

  // End of Table
  VirtualMemoryTable[++Index].PhysicalBase  = 0;
  VirtualMemoryTable[Index].VirtualBase     = 0;
  VirtualMemoryTable[Index].Length          = 0;
  VirtualMemoryTable[Index].Attributes      = (ARM_MEMORY_REGION_ATTRIBUTES)0;

  ASSERT((Index + 1) <= MAX_VIRTUAL_MEMORY_MAP_DESCRIPTORS);

  *VirtualMemoryMap = VirtualMemoryTable;
}
