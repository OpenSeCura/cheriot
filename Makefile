CHERIOT_ROOT = $(HOME)/work/cheriot

.PHONY: all verilog force

.DEFAULT_GOAL = all

CURR_DIR = $(shell pwd)
BINARY ?= $(CHERIOT_ROOT)/cheriot-rtos/examples/02.hello_compartment/build/cheriot/cheriot/release/hello_compartment

Binary.v: force
	@echo $(CURR_DIR)
	echo "From Stdlib Require Import List ZArith Zmod." > Binary.v
	echo "" >> Binary.v
	echo "Local Open Scope Z_scope." >> Binary.v
	echo "" >> Binary.v
	ENTRY_POINT=$$(python3 -c "import struct; f=open('$(BINARY)', 'rb'); f.seek(24); print(hex(struct.unpack('<I', f.read(4))[0]))"); \
	echo "Definition PcAddrInit : Z := $$ENTRY_POINT." >> Binary.v
	BASE_ADDR=$$(python3 -c "import struct; f=open('$(BINARY)', 'rb'); elf=f.read(); phoff, phnum = struct.unpack_from('<II', elf, 28)[0], struct.unpack_from('<H', elf, 44)[0]; print(hex(min(struct.unpack_from('<I', elf, phoff + i*32 + 8)[0] for i in range(phnum) if struct.unpack_from('<I', elf, phoff + i*32)[0] == 1)))"); \
	echo "Definition MemStartAddr : Z := $$BASE_ADDR." >> Binary.v
	TOHOST_ADDR=$$($(CHERIOT_ROOT)/llvm-project/builds/cheriot-llvm/bin/llvm-objdump -t $(BINARY) | awk '$$NF == "tohost" {print $$1}'); \
	echo "Definition tohostAddr : Z := 0x$$TOHOST_ADDR." >> Binary.v
	echo "" >> Binary.v
	echo "Definition binary: list Z := (" >> Binary.v
	$(CHERIOT_ROOT)/llvm-project/builds/cheriot-llvm/bin/llvm-objcopy -O binary $(BINARY) $(CURR_DIR)/tmp && cd $(CURR_DIR)
	hexdump -e '1/1 "0x%02x " "::\n"' -v tmp >> Binary.v
	rm tmp
	echo "nil)." >> Binary.v

coq: Makefile.coq.all Binary.v
	$(MAKE) -j -C ../Guru coq
	$(MAKE) -f Makefile.coq.all

all: coq
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/ $(CURR_DIR)/Clut/"

verilog: coq
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/Clut/" verilog

sim: coq
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/" sim

Makefile.coq.all: force
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.coq.all

force:

clean:: Makefile.coq.all
	$(MAKE) -C ../Guru clean
	$(MAKE) -f Makefile.coq.all clean
	find . -type f -name '*.v.d' -exec rm {} \;
	find . -type f -name '*.glob' -exec rm {} \;
	find . -type f -name '*.vo' -exec rm {} \;
	find . -type f -name '*.vos' -exec rm {} \;
	find . -type f -name '*.vok' -exec rm {} \;
	find . -type f -name '*.~' -exec rm {} \;
	find . -type f -name '*.hi' -exec rm {} \;
	find . -type f -name '*.o' -exec rm {} \;
	find . -type f -name '*.aux' -exec rm {} \;
	find . -type f -name 'Compile.hs' -exec rm {} \;
	find . -type f -name 'Main' -exec rm {} \;
	find . -type f -name 'Main.sv' -exec rm {} \;
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
	rm -f .nia.cache .lia.cache
	rm -f Binary.v

