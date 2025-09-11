# Disclosure of generative AI usage

(This document is updated every so often with possible new changes)

In parts of the project, generative AI, like LLM models from OpenAI were used.
It is the opinion of the author that its effective use for certain tasks is a
skill, and should receive here as much critical thinking as performing the
task without aid would receive. Learning its exact limitations and capabilities,
and by extension when and how to use it, and not use it, is in the authors
opinion a more viable long-term position than occluding any issue a priori.
Below the usage is detailed.

Note: This work is a master thesis project at the Graduate School of Natural
Sciences at Utrecht University. Per the institution's rules, use of generative
AI is allowed as long as the supervisors agree that for the particular level of
use, they can still properly assess the student's skills and other evaluation
points. As such, the level of AI usage has been discussed with my supervisors,
and agreed upon by them.


## Coding

This pertains to all code, principally `.lean` files. Larger explanatory or
discussive text in comments in these code files falls under the category 'Writing'
below.

The use for this category is **code completion + next-edit suggestions**. In
this mode, LLM's may suggest next words or lines to be written. In addition,
next-edit suggestions may suggest this insertion of text in other places in the
same document, and deletion of parts.

This mode has been tried in early 2025, but has been turned off after several
months of use, as the suggestions were often poor quality (like suggesting to
perform the `clear h` tactic after a `subst h`), and where hence often a
hinderance. Frequently new models are arriving in 2025, so mileage very well
varies, and I may enable it again every so often to keep learning about the AI's
capabilities and limitations.

We did _not_ use any agentic help. In this mode, LLM's are equipped with tools
with which they can browse your code base and suggest complete rewrites of code
and introduce new files. Furthermore, it is prompt-based, and multiple
prompts are possible (often needed), to refine the edits or take the task a step
further. A special case is when any equipped tools are disconnected from the
main work, this is often called a 'chat bot', and is often accessed through a
website or mobile app. Notable examples include ChatGPT.com and chat.mistral.ai.

The use of agentic help is often superior in output quality compared to code
completion and next-edit suggestions, given the improved context, tooling, and
explicit instructions. Furthermore, so-called 'reasoning models' are usually
reserved for this agentic help, as their computational intensity and execution
duration are far higher than their 'non-reasoning' counterparts.

During 2025, we observed major shifts and jumps in agentic AI capabilities for
code writing. As a result, we have decided not to employ agentic AI capabilities
for coding; the exact boundaries of its latest capabilities are not common
knowledge throughout society and the academic world, hence hindering assessments
regarding human contribution, skills gained, and skills possessed by the author.
Even more, the ever-changing abilities over time would make it hard to assess
exactly what level of help the AI could have provided at each stage in the
project.

## Writing

This pertains to all explanatory and discussive texts. Snippets of code
throughout such texts fall under the category 'Coding'. Together with the
categories 'Coding' and 'Research', it comprises the entire editorial body of
the work. For example, the way work is presented, its structure and order of
chapters, and the examples given all fall under the category Writing, or in some
cases under Coding. The latter could occur when AI suggests function names or
file paths for files.

The use for this category is **none** (see minor exceptions below). We think AI
capabilities are currently not developed enough to produce valuable high-quality
academic texts. Furthermore, the contents of academic works are tightly bound
to the in-depth knowledge, experience, and critical thinking of the author. As
such, any possible proper use would involve explaining everything meticulously
to the AI model already, hence little gain would be achieved. The use of AI can
sometimes be used to reword, expand or summarise text. The author prefers to do
such tasks themselves, and has reservations on its ability to perform these
tasks without losing important nuances and keeping adequate information density.

Some minor exceptions exist. This is for example when the author is searching
for a particular word to capture some thought. Another example could be making
a diagram and using AI tools to move contents around in a particular way. Other
uses would be to a similar degree. In each case, any change is meticulously
reviewed and verified by the author before being accepted in the work.

## Research

This pertains to accumulating external information which influence the editorial
processes. For example, searching for mathematical theories or coding libraries
that are relevant to the subject, and embedding their knowledge in this work.

The use of this category is currently **none**, but minor agentic use may be
possible. In this case, a search engine's 'AI summary' or a chatbot's answer
may be used to find clues or proper terminology of a subject. Any information
will only be incorporated in the work if a credible non-AI source is found
backing the statement.


## Administrational

This pertains to tasks outside of the academic and the scientific scope. That
is, only stylistic, with no editorial impact.

The use for this is **agentic**. For example, I have once asked a chatbot to
write me a `sed` command to perform certain syntactical replacements in my
document. Other possible future uses could be scaffolding a website for
exhibiting the work and its documentation. The use has so far been very limited
to a few times.

