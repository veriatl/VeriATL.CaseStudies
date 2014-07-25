VeriATL: Verifying the Operational Correctness of ATL Transformations through a Formal Semantics for the ATL Virtual Machine.
=======

Introduction
------

In this work, we develop an approach for verifying that the standard implementation of an ATL model transformation satisfies its declarative definition. The goal is to establish an operational correctness relationship between the declarative transformation definition, as it appears in the ATL matched rules, and its operational implementation in terms of bytecode instructions for the ATL virtual machine. Thus, we develop a library for explaining the metamodel and OCL constructs that are involved in the ATL transformation, and the formal semantics of the ATL virtual machine. These are encapsulated in a verification system, named VeriATL. The system automatically translates both the ATL matched rules and the corresponding bytecode instructions into the Boogie intermediate verification language, which in turn provides access to the Z3 theorem prover. The experiments with VeriATL demonstrate the feasibility of this approach. They also illustrate how VeriATL can automatically identify conflicts among the ATL matched rules and termination proofs.


The Source Files for ATL Transformation
------


In this section, the source files for ATL transformation is presented, which consists of 2 metamodels(ER and REL), and 6 ATL matched rules. They form the input of VeriATL verification system.

Source & Target Metamodel
ATL Transformation Specification

The Generated Boogie files
------
The source files for ATL transformation is translated into the following Boogie files, which are send to the Boogie verifier to verify the operational correctness of ATL matched rules. Our verification result is a either a confirmation that the ATL matched rules are operationally correct, or trace information from Boogie verifier that leads to the operational incorrectness.

Metamodels
ATL Rules:
S2S: Apply / Match
E2R: Apply / Match
R2R: Apply / Match
EA2A: Apply / Match
RA2A: Apply / Match
RA2AK: Apply / Match


The Auxiliary Boogie Files
------

During the verification of operational correctness of ATL matched rules, the following Boogie library needs to be imported:

ASM Bytecode Axiomatization
Library for OCL
ATL-specific Library Axiomatization

How to Use
------
First, here is package that contains all the files to reproduce the verification result. [Download]

One way to reproduce the verification result is when the user have the Boogie & Z3 installed, using the following command:

boogie.exe Preludes/LibOCL.bpl Preludes/NativeLib.bpl Preludes/instr.bpl Metamodels.bpl $(FILE_NAME)

e.g.
boogie.exe Preludes/LibOCL.bpl Preludes/NativeLib.bpl Preludes/instr.bpl Metamodels.bpl matchS2S.bpl
