# Sylow-Theorems-group-project

This repository contains our group project for the **2025/26 Warwick MA4N1: *Theorem Proving with Lean*** module.  
Our goal is to formally prove the **Sylow Theorem** using Lean.

During the proof development, we follow the structure and arguments presented in the **Warwick MA3K4: Introduction to Group Theory** lecture notes, in particular **Chapter 3: The Sylow theorems**.  
Reference link:  
[MA3K4 Lecture Notes](https://moodle.warwick.ac.uk/course/view.php?id=71701)

---

## Project Outline

We divide the overall proof into several components to enable modular development and parallel work.  
The full outline and plan of the project can be found here:  
[Project Outline](./Project_Outline.pdf)

[Project Plan](./Sylow_Plan.pdf)

## Project Structure

The repository is organised in a modular way, reflecting the logical structure of the proof of the Sylow Theorems and allowing different components to be developed independently.

### Core Background Files

The following files contain **preliminary definitions, lemmas, and standard results** required for the formalisation of the Sylow Theorems.  
They serve as foundational material and are reused throughout the project.

- `Bijectivity Statements.lean`  
- `Lagrange.lean`  
- `NumberTheory.lean`  
- `OrbitStabiliser.lean`  

These files formalise key results from group theory and number theory, such as bijections, Lagrange’s Theorem, basic number-theoretic lemmas, and the Orbit–Stabiliser Theorem, which are essential prerequisites for the proof of Sylow’s Theorem.

---

### Intermediate Claims and Lemmas

The following files correspond to **individual claims, lemmas, and intermediate steps** in the proof of the Sylow Theorems.  
They closely follow the structure of the arguments presented in the MA3K4 lecture notes.

- `Claim1.lean`  
- `Claim 2 plus 9&10.lean`  
- `claim 2_orb_2.lean`  
- `claim24pt1&2.lean`  

Each file focuses on a specific logical component of the overall proof, making the development easier to manage and verify.

---

### Final Integration

- `all together.lean`

This file integrates the results from all previous files and assembles them into a complete formal proof of the **Sylow Theorems**, together with related consequences.
