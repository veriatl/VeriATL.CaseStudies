A Sound Execution Semantics for ATL via Translation Validation
=======

Introduction
------
In this work we present a translation validation approach to encode a sound execution semantics for the ATL specification. Based on our sound encoding, the goal is to reliably verify the ATL specification against the specified OCL contracts. To demonstrate our approach, we have developed the VeriATL verification system using the Boogie2 intermediate verification language, which in turn provides access to the Z3 theorem prover. Our system automatically encodes the execution semantics of each ATL specification, as it appears in the ATL matched rules, into the intermediate verification language. Then, to ensure the soundness of the encoding, we verify that it faithfully represents the runtime behaviour of its corresponding compiled implementation in terms of bytecode instructions for the ATL virtual machine. This repository contains the experimenting details for VeriATL system.


Overview of Repository
------
1. Libraries
2. The Source Files for ATL Transformation
3. Encoding soundness verification
4. Transformation contracts verification
5. Regression Tests + Driver + Result

Libraries
------
VeriATL system is driven by two essential Boogie Libraries:
- Library for Metamodel & OCL [portal]()
- Library for ASM bytecode formalisation [portal]()

The Source Files for ATL Transformation
------
We demonstrate VeriATL system against ER2REL transformation. The source files of this transformation contain:
- Source (ER-Diagram) and target (RELational-Schema) metamodels [portal]()
- ER2REL transformation specification in ATL [portal]()
- The compiled ER2REL transformation in ASM [portal]()

Verifying sound encoding of ATL rules
------
Both metamodels and ATL specification are encoded in Boogie for verifying sound encoding of ATL rules.
- metamodels [portal]()
- ATL rules [portal]()


Transformation contracts verification
------
Using the sound encoding of ATL rules, we can verify transformation specification against transformation contracts. We verify ER2REL transformation against 4 OCL contracts. The focus here is to demonstrate OCL contracts encoding and transformation rules scheduling.
1. The uniqueness of *RELSchema*s' name [portal]()
2. The uniqueness of *Relation*s' name in *RELSchema* [portal]()
3. The uniqueness of *RELAttribute*s' name in *Relation* [portal]()
4. The existence of *Relation*s' *key* in *RELAttribute* [portal]()

To modularize the verification task, the encodings of ATL rules are encapsulated in this file [portal]().


Regression Tests + Test Driver + Result
------
Finally, to ensure validity of our approach. The [regression tests]() are executed on every modification of Boogie libraries, or modifications to the Boogie code compilation process (i.e. OCL compilation, ATL rules compilation and ASM code compilation to Boogie). A [test driver]() written in Python is provided to run regression tests. It needs Boogie installed [HowTo](https://boogie.codeplex.com/wikipage?title=Binaries).

We also record the result [portal]() and performance [portal]() of regression tests in XML for people who interested.


------


