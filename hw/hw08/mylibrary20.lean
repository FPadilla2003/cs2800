-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .mylibrary18


-- subtraction on nats: 
def minus : nat -> nat -> nat 
    | 0 _ := 0
    | (nat.succ x) 0 := (nat.succ x)
    | (nat.succ x) (nat.succ y) := minus x y



theorem and_distrib_or: ∀ A B C : Prop, A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C) 
:= begin
-- ANSWER:
    intros,
    split,
    {
        intro a,
        cases a,
        cases a_right,
        {
            left,
            split,
            assumption,
            assumption,
        },
        {
            right,
            split,
            assumption,
            assumption,
        },
    },
    {
        intro a,
        cases a,
        {
            cases a,
            split,
            assumption,
            left,
            assumption,
        },
        {
            cases a,
            split,
            assumption,
            right,
            assumption,
        }
    }
end

theorem or_distrib_and: ∀ A B C : Prop, (A ∨ (B ∧ C)) ↔ ((A ∨ B) ∧ (A ∨ C))
-- ANSWER:
:= begin
    intros,
    split,
    {
        intro a,
        cases a,
        {
            split,
            left, assumption,
            left, assumption,
        },
        {
            cases a,
            split,
            right, assumption,
            right, assumption,
        }
    },
    {
        intro a,
        cases a,
        cases a_left,
        {
            left,
            assumption,
        },
        {
            cases a_right,
            {
                left,
                assumption,
            },
            {
                right,
                split,
                assumption,
                assumption,
            }
        }
    }
end

theorem not_not_p_implies_p_using_em: ∀ P : Prop, (¬ ¬ P) → P 
:= begin
    intro,
    intro h1,
    have h2 := classical.em P, -- we are "calling" classical.em with argument P
    cases h2,
    {
        assumption,
    },
    {
        have h3 := h1 h2,
        trivial,
    }
end

lemma not_not (p : Prop) : p ↔ ¬ ¬ p 
:= begin
  split,
  {
    intro h,
    intro h2,
    contradiction,
  },
  have h := not_not_p_implies_p_using_em p,
  exact h,
end

theorem not_p_or_q_iff_p_implies_q: 
    ∀ p q : Prop, (¬p ∨ q) ↔ (p → q)
:= begin
  intros,
  split,
  have h1 := not_or_implies p q,
  assumption,
  have h2 := implies_not_or p q ,
  assumption,
end

lemma deMorgan1: ∀ (p q : Prop), (¬ p ∧ ¬ q) → ¬ (p ∨ q) 
:= begin
-- ANSWER:
-- constructive logic suffices:
  intro,
  intro,
  intro a,
  intro a_1,
  cases a with h1 h2,
  cases a_1,
  {
    have h3 := h1 a_1,
    contradiction,
  },
  {
    have h3 := h2 a_1,
    contradiction,
  }
end

lemma deMorgan2: ∀ (p q : Prop), (¬ p ∨ ¬ q) → ¬ (p ∧ q) 
:= begin
-- ANSWER:
-- constructive logic suffices:
  intro,
  intro,
  intro a,
  intro a_1,
  cases a_1 with h1 h2,
  cases a,
  {
    have h3 := a h1,
    contradiction,
  },
  {
    have h3 := a h2,
    contradiction,
  }
end

lemma deMorgan3: ∀ (p q : Prop), ¬ (p ∨ q) → (¬ p ∧ ¬ q) 
:= begin
-- ANSWER:
-- constructive logic suffices:
  intro,
  intro,
  intro h1,
  split,
  {
    intro h2,
    have h3 : p ∨ q := begin left, assumption, end,
    have h4 := h1 h3,
    contradiction,
  },
  {
    intro h2,
    have h3 : p ∨ q := begin right, assumption, end,
    have h4 := h1 h3,
    contradiction,
  }
end

lemma deMorgan4: ∀ (p q : Prop), ¬ (p ∧ q) → (¬ p ∨ ¬ q) 
:= begin
-- ANSWER:
-- for this last one, we need classical logic: constructive/intuitionistic logic is not enough:
  intro,
  intro,
  intro a,
  cases classical.em p, -- here we use law of excluded middle, they don't know this yet, so OK to stop here! 
  -- also OK if they used it because we talked about it on Wed 18 Oct 2023
  {
    right,
    intro,
    have h1 : p ∧ q := begin
      split,
      assumption,
      assumption,
    end,
    have h2 := a h1,
    contradiction,
  },
  {
    left,
    assumption,
  }
end

theorem deMorgan_or: ∀ p q : Prop, ¬ (p ∨ q) ↔ (¬p ∧ ¬q)
:= begin
-- ANSWER:
  intros,
  split,
  {
    have h := deMorgan3 p q,
    assumption,
  },
  {
    have h := deMorgan1 p q,
    assumption,
  }
end

theorem deMorgan_and: ∀ p q : Prop, ¬ (p ∧ q) ↔ (¬p ∨ ¬q) 
:= begin
-- ANSWER:
  intros,
  split,
  {
    have h := deMorgan4 p q,
    assumption,
  },
  {
    have h := deMorgan2 p q,
    assumption,
  }
end

-- simplifying if-then-else expressions

lemma itetrue (p : Prop) [decidable p] : 
  p → ∀ T : Type, ∀ x y : T, (if p then x else y) = x
:= begin
  intros h T x y,
  simp [h],
end

lemma itefalse (p : Prop) [decidable p] : 
  ¬p → ∀ T : Type, ∀ x y : T, (if p then x else y) = y
:= begin
  intros h T x y,
  simp [h],
end
