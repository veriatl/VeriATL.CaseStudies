A Sound Execution Semantics for ATL via Translation Validation
=======

Introduction
------
In this work we present a translation validation approach to encode a sound execution semantics for the ATL specification. Based on our sound encoding, the goal is to reliably verify the ATL specification against the specified OCL contracts. To demonstrate our approach, we have developed the VeriATL verification system using the Boogie2 intermediate verification language, which in turn provides access to the Z3 theorem prover. Our system automatically encodes the execution semantics of each ATL specification, as it appears in the ATL matched rules, into the intermediate verification language. Then, to ensure the soundness of the encoding, we verify that it faithfully represents the runtime behaviour of its corresponding compiled implementation in terms of bytecode instructions for the ATL virtual machine. This repository contains the experimenting details for VeriATL system.


Overview of Repository
------
1. Libraries
2. Encoding soundness verification
3. Case Studies
4. Regression Tests + Driver + Result

Libraries
------
VeriATL system is driven by two essential Boogie Libraries:
- Library for Metamodel & OCL [portal](https://github.com/VeriATL/VeriATL/blob/master/Prelude/LibOCL.bpl)
- Library for ASM bytecode formalisation [portal](https://github.com/VeriATL/VeriATL/blob/master/Prelude/Instr.bpl)
- Auxiliary Library for ATL native API [portal](https://github.com/VeriATL/VeriATL/blob/master/Prelude/NativeLib.bpl)

Case Studies
------
Currently, we apply VeriATL on four case studies
- ER2REL - ER diagram to Relational schema. [portal](https://github.com/VeriATL/VeriATL/tree/master/_ER2REL)
- HSM2FSM - Hierarchical State Machine to Flatten State Machine. [portal](https://github.com/VeriATL/VeriATL/tree/master/_HSM2FSM)
- ResolveTemp - to demonstrate ResolveTemp operation of ATL. [portal](https://github.com/VeriATL/VeriATL/tree/master/_ResolveTemp)
- Resolving Algorithm - to verify the functional correctness of resolving algorithm of ATL.
[portal](https://github.com/VeriATL/VeriATL/tree/master/_Resolving_Algorithm)

These case studies are organized into:
- Metamodels encoding, in the directory of /Metamodel/
- Executional Semantics of ATL transformation, in the directory of /ExecutionSemantics/
- Source code of each case study, in the directory of /Sources/
- Oracle of UnitTesting, in the directory of /UnitTesting/
- Boogie code for transformation correctness, in the directory of /ATL_Correctness/
- Boogie code for translation validation, in the directory of /ATL_Rule_Encoding/



Regression Tests + Test Driver + Result
------
Finally, to ensure validity of our approach. The regression are executed on every modification to the Boogie libraries, or modifications to the Boogie code compilation process (i.e. OCL compilation, ATL rules compilation and ASM code compilation to Boogie). A [test driver](https://github.com/VeriATL/VeriATL/blob/master/UnitTestingDriver/testDriver.py) written in Python is provided to run regression tests. It needs Boogie installed [HowTo](https://boogie.codeplex.com/wikipage?title=Binaries).

We also record the result and performance of regression tests for reader who interested. They can be found in the /UnitTesting/ directory of each case study.

Link to VeriGT
------
VeriGT is a verifier to verify the functional correctness of SimpleGT graph transformations. SimpleGT is an experimental graph transformation language that is based on the EMFTVM bytecode language ([Portal](https://wiki.eclipse.org/ATL/EMFTVM), which can be seen as a superset of ASM). The VeriGT project can be found at [Portal](https://github.com/veriatl/VeriGT).

