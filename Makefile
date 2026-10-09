# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

.PHONY: all rtl rtlexe simrtl simrtlexe force

.DEFAULT_GOAL = all

CURR_DIR = $(shell pwd)

Makefile.coq.all: force
	$(COQBIN)rocq makefile --no-rocq-package-warning -docroot Cheriot -f _CoqProject -o Makefile.coq.all

coq: Makefile.coq.all
	$(MAKE) -j -C ../Guru coq
	$(MAKE) -f Makefile.coq.all

all: coq
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/ $(CURR_DIR)/Impl/ $(CURR_DIR)/Clut/"

rtl: coq
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/Impl/ $(CURR_DIR)/Clut/" rtl

rtlexe: rtl
	verilator -Wno-CMPCONST --top Tb --binary -I../Guru/Verilog -I./Impl --Mdir Impl/obj_dir Impl/Tb.sv
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/Clut/" rtlexe

simrtl: coq
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/ $(CURR_DIR)/Impl/ $(CURR_DIR)/Clut/" simrtl

simrtlexe: simrtl
	verilator -Wno-CMPCONST --top Tb --binary -I../Guru/Verilog -I. --Mdir sim_obj_dir SimTb.sv
	verilator -Wno-CMPCONST --top Tb --binary -I../Guru/Verilog -I./Impl --Mdir Impl/sim_obj_dir Impl/SimTb.sv
	$(MAKE) -C ../Guru TARGETS="$(CURR_DIR)/Clut/" simrtlexe

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
	find . -type f -name '*.ho' -exec rm {} \;
	find . -type f -name 'Compile.hs' -exec rm {} \;
	find . -type f -name 'Rtl' -exec rm {} \;
	find . -type f -name 'Rtl.sv' -exec rm {} \;
	find . -type f -name 'SimRtl.sv' -exec rm {} \;
	find . -type d -depth -name 'obj_dir' -exec rm -rf {} \;
	find . -type d -depth -name 'sim_obj_dir' -exec rm -rf {} \;
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
	rm -f .nia.cache .lia.cache

