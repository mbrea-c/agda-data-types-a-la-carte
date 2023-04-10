# Data types à la carte in Agda

Proof-of-concept Agda implementation of the _Data types à la carte_ framework, including a simple example and a
partial application to a formal treatment of the Simply Typed Lambda Calculus which shows
where the first significant roadblocks are encountered.

The agda files are:
 - `DataTypesALaCarte.agda` --- contains the common framework for the DTALC method. Disables strict positivity checking for the fixed-point of functors and termination checking for folding: a more sophisticated solution is required to circumvent these issues.
 - `SimpleExample.agda` --- simple algebra used an an example in the original DTALC paper, together with working evaluator.
 - `LambdaCalc.agda` --- very incomplete attempt at applying DTALC to the STLC.
