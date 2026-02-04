# Sylow-Theorems-group-project

This repository contains our group project for the **2025/26 Warwick MA4N1: *Theorem Proving with Lean*** module.  
Our goal is to formally prove the **first and fourth Sylow Theorem** using Lean.

During the proof development, we follow the structure and arguments presented in the **Warwick MA3K4: Introduction to Group Theory** lecture notes, in particular **Chapter 3: The Sylow theorems**.  
Reference link:  
[MA3K4 Lecture Notes](https://moodle.warwick.ac.uk/course/view.php?id=71701)

---

## Project Outline

We divide the overall proof into several components to enable modular development and parallel work.  
The full outline and plan of the project can be found here:  

[Project Outline](./Project_Outline.pdf)

[Project Plan](./Sylow_Plan.pdf)

There are theorem names and comments throughout our code that may reference numbers. These correspond to the numbered intermediate results in the above 'Project Plan' file.

### Independent sub-projects

The following files contain **preliminary definitions and intermediate results** required for the formalisation of the Sylow Theorems. Each corresponds to some section of the proof from MA3K4.
They serve as foundational material and are reused throughout the project. We divided tasks between us so we could work in parallel on different parts of the project.

- `Bijectivity Statements.lean`  
- `Lagrange.lean`  
- `NumberTheory.lean`  
- `OrbitStabiliser.lean`
- `Claim1.lean`  
- `Claim 2 plus 9&10.lean`  
- `claim 2_orb_2.lean`  
- `claim24pt1&2.lean`  

---

### Final Integration

- `all together.lean`

There is little content in previously mentioned files that is not also in the `all together.lean` file.

This file integrates the results from all previous files and attempts to assemble them into a proof of the first and fourth Sylow Theorems.
We were working on different sections in parallel, as such there are several type conflicts that we did not have time to resolve when combining our work. Some theorems are sorry'd as a result.
