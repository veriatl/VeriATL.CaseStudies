A Sound Execution Semantics for ATL via Translation Validation
=======

Introduction
------
In this work we present a translation validation approach to encode a sound execution semantics for the ATL specification. Based on our sound encoding, the goal is to reliably verify the ATL specification against the specified OCL contracts. To demonstrate our approach, we have developed the VeriATL verification system using the Boogie2 intermediate verification language, which in turn provides access to the Z3 theorem prover. Our system automatically encodes the execution semantics of each ATL specification, as it appears in the ATL matched rules, into the intermediate verification language. Then, to ensure the soundness of the encoding, we verify that it faithfully represents the runtime behaviour of its corresponding compiled implementation in terms of bytecode instructions for the ATL virtual machine. This repository contains the experimenting details for VeriATL system.


Overview of ER2REL Case Study
------

1. The Source Files for ATL Transformation
2. Encoding soundness verification
3. Transformation contracts verification
4. Regression Tests + Driver + Result


The Source Files for ATL Transformation
------
We demonstrate VeriATL system against ER2REL transformation. The source files of this transformation contain:
- Source (ER-Diagram) and target (RELational-Schema) metamodels [portal](https://github.com/VeriATL/VeriATL/tree/master/_ER2REL/Sources)
- ER2REL transformation specification in ATL [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/Sources/er2rel.atl)
- The compiled ER2REL transformation in ASM [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/Sources/er2rel.asm)

Verifying sound encoding of ATL rules
------
Our main contribution is verifying the soundness of our encoding for the execution semantics of ATL rules. To perform this verification, both metamodels and ATL specification are encoded in Boogie.
- metamodels [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/Metamodel/Metamodels.bpl)
- **ATL rules** [portal](https://github.com/VeriATL/VeriATL/tree/master/_ER2REL/ATL_Rule_Encoding)


Transformation contracts verification
------
Using the sound encoding of ATL rules, we can verify transformation specification against transformation contracts. We verify ER2REL transformation against 4 OCL contracts. The focus here is to demonstrate OCL contracts encoding and transformation rules scheduling:

1. The uniqueness of *RELSchema*s' name [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/ATL_Correctness/ER2REL_Correctness_post1.bpl)
2. The uniqueness of *Relation*s' name in *RELSchema* [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/ATL_Correctness/ER2REL_Correctness_post2.bpl)
3. The uniqueness of *RELAttribute*s' name in *Relation* [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/ATL_Correctness/ER2REL_Correctness_post3.bpl)
4. The existence of *Relation*s' *key* in *RELAttribute* [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/ATL_Correctness/ER2REL_Correctness_post4.bpl)

To modularize the verification task, the encodings of ATL rules are encapsulated in this file [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/ExecutionSemantics/ATLRules.whole.bpl).


Regression Tests
------
The [regression tests](https://github.com/VeriATL/VeriATL/tree/master/_ER2REL/UnitTesting) are executed on every modification to the Boogie libraries, or modifications to the Boogie code compilation process (i.e. OCL compilation, ATL rules compilation and ASM code compilation to Boogie). 

We also record the **result** [portal](https://github.com/VeriATL/VeriATL/blob/master/_ER2REL/UnitTesting/RegressionResult.txt) and **performance** [portal](https://github.com/VeriATL/VeriATL/tree/master/_ER2REL/UnitTesting/PerformanceData) of regression tests for reader who interested.


------


