-- CS 2800 LOGIC AND COMPUTATION, FALL 2023
-- COPYRIGHT 2023 STAVROS TRIPAKIS -- DO NOT DISTRIBUTE!

import .mylibrary14 

def app : list ℕ → list ℕ → list ℕ 
  | [] L := L 
  | (x :: L1) L2 := x :: (app L1 L2)
--

theorem plus_0_x: ∀ x : nat, plus 0 x = x 
:= begin
    intro,
    refl,
end

lemma p_and_true: ∀ P : Prop, (P ∧ true) ↔ P 
:= begin
  intros p,
  split,
  {
    intro h,
    cases h with h1 h2,
    exact h1,
  },
  {
    intro h,
    split,
      assumption,
      trivial,
  },
end

lemma p_or_true: ∀ P : Prop, (P ∨ true) ↔ true 
:= begin
  intro,
  split,
  {
    intro h,
    trivial,
  },
  {
    intro h,
    right,
    trivial,
  },
end

theorem p_and_q_implies_q_and_p: ∀ p q : Prop, (p ∧ q) → (q ∧ p) 
:= begin
  intros p q,
  intro h,
  cases h with h1 h2,
  split,
  {
    exact h2,
  },
  {
    exact h1,
  },
end

theorem p_and_q_iff_q_and_p: ∀ p q : Prop, (p ∧ q) <-> (q ∧ p) 
:= begin
  intros p q,
  have h1 := p_and_q_implies_q_and_p p q,
  have h2 := p_and_q_implies_q_and_p q p,
  split,
  exact h1,
  exact h2,
end

theorem not_or_implies: forall A B : Prop,   (¬A ∨ B) -> (A -> B)
:= begin
    intro,
    intro,
    intro h1,
    intro h2,
    cases h1,
        {
            have h3 := h1 h2,
            contradiction,
        },
        {
            exact h1,
        },
    -- DONE! we didn't have to use classical.em 
end

theorem implies_not_or: forall A B : Prop,   (A -> B) -> (¬A ∨ B)
:= begin
    intro,
    intro,
    intro h1,
    cases classical.em A,
    {
        have h2 := h1 h,
        right,
        exact h2,
    },
    {
        left,
        exact h,
    },
end

theorem implies_iff_not_or: forall A B : Prop,   (A -> B) <-> (¬A ∨ B)
:= begin
  intros,
  split,
  have h1 := implies_not_or A B,
  exact h1, 
  have h2 := not_or_implies A B,
  exact h2,
end

lemma succeq: ∀ x y : ℕ, (nat.succ x) = (nat.succ y) ↔ x = y 
:= begin
  intros,
  split,
  intro h,
  simp at h,
  assumption,
  intro h,
  rw h,
end


lemma listeq: ∀ x y : ℕ, ∀ L1 L2 : list ℕ, (x :: L1) = (y :: L2) ↔ ((x = y) ∧ (L1 = L2))
:= begin
  intros,
  split,
  {
    intro h,
    simp at h,
    assumption,
  },
  {
    intro h,
    simp,
    assumption,
  },
end
