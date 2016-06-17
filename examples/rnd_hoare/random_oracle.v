Class RandomOracle: Type := {
  ro_question: Type;
  ro_answer: ro_question -> Type;
  ro_default_question: ro_question;
  ro_default_answer: ro_answer ro_default_question
}.

Definition RandomQA {ora: RandomOracle}: Type := {q: ro_question & ro_answer q}.

