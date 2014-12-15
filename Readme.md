A Sound Execution Semantics for ATL via Translation Validation
=======

Introduction
------
In this work we present a translation validation approach to encode a sound execution semantics for the ATL specification. Based on our sound encoding, the goal is to reliably verify the ATL specification against the specified OCL contracts. To demonstrate our approach, we have developed the VeriATL verification system using the Boogie2 intermediate verification language, which in turn provides access to the Z3 theorem prover. Our system automatically encodes the execution semantics of each ATL specification (as it appears in the ATL matched rules) into the intermediate verification language. Then, to ensure the soundness of the encoding, we verify that it faithfully represents the runtime behaviour of its corresponding compiled implementation in terms of bytecode instructions for the ATL virtual machine. The experiments demonstrate the feasibility of our approach. They also illustrate how to automatically verify an ATL specification against specified OCL contracts.


The Source Files for ATL Transformation
------
In this section, the source files for ATL transformation is presented, which consists of 2 metamodels(ER and REL), and the ATL specification. They form the input of VeriATL verification system.

- [Source](https://github.com/VeriATL/VeriATL/blob/master/sources/ER.ecore) & [Target Metamodel](https://github.com/VeriATL/VeriATL/blob/master/sources/REL.ecore)
- [ATL Transformation Specification](https://github.com/VeriATL/VeriATL/blob/master/sources/er2rel.atl)

The Generated Boogie files
------
TBW

- [Metamodels](https://github.com/VeriATL/VeriATL/blob/master/Metamodels.bpl)
- [ATL Rules](https://github.com/VeriATL/VeriATL/tree/master/generated)


The Auxiliary Boogie Files
------

TBW

- [ASM Bytecode Axiomatization](https://github.com/VeriATL/VeriATL/blob/master/instr.bpl)
- [Library for OCL](https://github.com/VeriATL/VeriATL/blob/master/LibOCL.bpl)
- [ATL-specific Library Axiomatization](https://github.com/VeriATL/VeriATL/blob/master/NativeLib.bpl)


Test Suites
------
TBW

Todo
------
TBW

How to Use
------
One way to reproduce the verification result is when the user have the Boogie & Z3 installed, using the following command:

* boogie.exe Preludes/LibOCL.bpl Preludes/NativeLib.bpl Preludes/instr.bpl Metamodels.bpl $(FILE_NAME)

e.g.
* boogie.exe Preludes/LibOCL.bpl Preludes/NativeLib.bpl Preludes/instr.bpl Metamodels.bpl matchS2S.bpl