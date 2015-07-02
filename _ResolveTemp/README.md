A Sound Execution Semantics for ATL via Translation Validation (Extended Case Study)
=======

Introduction
------
In this work we present a translation validation approach to encode a sound execution semantics for the ATL specification. Based on our sound encoding, the goal is to reliably verify the ATL specification against the specified OCL contracts. To demonstrate our approach, we have developed the VeriATL verification system using the Boogie2 intermediate verification language, which in turn provides access to the Z3 theorem prover. Our system automatically encodes the execution semantics of each ATL specification, as it appears in the ATL matched rules, into the intermediate verification language. Then, to ensure the soundness of the encoding, we verify that it faithfully represents the runtime behaviour of its corresponding compiled implementation in terms of bytecode instructions for the ATL virtual machine. This repository contains the experimenting details for VeriATL system.

This repository holds our third case study for VeriATL - to demonstrate how to handle ResolveTemp operation in ATL.
