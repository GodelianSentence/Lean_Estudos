open Classical
variable (p q r : Prop)

-- commutatividade de ∧ e ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    have hq := h.right
    have hp := h.left
    exact And.intro hq hp
  . intro h
    have hp := h.right
    have hq := h.left
    exact And.intro hp hq
example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    intro hp
    exact Or.inr hp
    intro hq
    exact Or.inl hq
  . intro h
    apply Or.elim h
    intro hq
    exact Or.inr hq
    intro hp
    exact Or.inl hp

-- associatividade de ∧ e ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    have hpq := h.left
    have hr := h.right
    exact And.intro (hpq.left) (And.intro (hpq.right) hr)
  . intro h
    have hp := h.left
    have hqr := h.right
    exact And.intro (And.intro hp (hqr.left)) hqr.right
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hpq
      apply Or.elim hpq
      . intro hp
        exact Or.inl hp
      . intro hq
        exact Or.inr (Or.inl hq)
    . intro hr
      exact Or.inr (Or.inr hr)
  . intro h
    apply Or.elim h
    . intro hp
      exact Or.inl (Or.inl hp)
    . intro hqr
      apply Or.elim hqr
      . intro hq
        exact Or.inl (Or.inr hq)
      . intro hr
        exact (Or.inr hr)

-- distributividade
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    have hp := h.left
    have hqr := h.right
    apply Or.elim hqr
    . intro hq
      exact Or.inl (And.intro hp hq)
    . intro hr
      exact Or.inr (And.intro hp hr)
  . intro h
    apply Or.elim h
    . intro hpq
      have hp := hpq.left
      have hq := hpq.right
      exact And.intro hp (Or.inl hq)
    . intro hpr
      have hp := hpr.left
      have hr := hpr.right
      exact And.intro hp (Or.inr hr)
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp
      exact And.intro (Or.inl hp) (Or.inl hp)
    . intro hqr
      have hq := hqr.left
      have hr := hqr.right
      exact And.intro (Or.inr hq) (Or.inr hr)
  . intro h
    have hpq := h.left
    have hpr := h.right
    apply Or.elim hpr
    . intro hp
      exact Or.inl hp
    . intro hr
      apply Or.elim hpq
      . intro hp
        exact Or.inl hp
      . intro hq
        exact Or.inr (And.intro hq hr)

-- outras propriedades
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h
    . intro hpq
      have hp := hpq.left
      have hq := hpq.right
      exact h hp hq
  . intro h
    . intro hp
      . intro hq
        exact h (And.intro hp hq)
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    apply And.intro
    (.  intro hp ; exact h (Or.inl hp))
    (.  intro hq ; exact h (Or.inr hq))
  . intro h
    have hpr := h.left
    have hqr := h.right
    . intro hpq
      apply Or.elim hpq
      . intro hp
        exact hpr hp
      . intro hq
        exact hqr hq
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply Or.elim (em p)
    . intro hp
      exact absurd (Or.inl hp) h
    . intro hnp
      apply Or.elim (em q)
      . intro hq
        exact absurd (Or.inr hq) h
      . intro hnq
        exact And.intro hnp hnq
  . intro h
    have hnp := h.left
    have hnq := h.right
    apply Or.elim (em (p ∨ q))
    . intro hpq
      apply hpq.elim
      . intro hp
        exact absurd hp hnp
      . intro hq
        exact absurd hq hnq
    . intro hnpq
      exact hnpq
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  . intro h
    apply Or.elim (em (p ∧ q))
    . intro hpq
      have hp := hpq.left
      have hq := hpq.right
      apply h.elim
      . intro hnp
        exact absurd hp hnp
      . intro hnq
        exact absurd hq hnq
    . intro hnpq
      exact hnpq
example : ¬(p ∧ ¬p) := by
  apply Or.elim (em (p ∧ ¬p))
  . intro hpnp
    have hp := hpnp.left
    have hnp := hpnp.right
    exact absurd hp hnp
  . intro nhpnp
    exact nhpnp
example : p ∧ ¬q → ¬(p → q) := by
  . intro h
    have hp := h.left
    have hnq := h.right
    apply Or.elim (em (p → q))
    . intro hpq
      exact absurd (hpq hp) hnq
    . intro nhpq
      exact nhpq
example : ¬p → (p → q) := by
  . intro hnp
    . intro hp
      apply Or.elim (em q)
      . intro hq
        exact hq
      . intro hnq
        exact absurd hp hnp
example : (¬p ∨ q) → (p → q) := by
  . intro h
    apply h.elim
    . intro hnp
      . intro hp
        exact h.neg_resolve_left hp
    . intro hq
      . intro hp
        exact hq
example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    apply Or.elim h
    . intro hp
      exact hp
    . intro hf
      exact hf.elim
  . intro h
    exact Or.inl h
example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro hpf
    exact hpf.right
  . intro hf
    exact hf.elim
example : (p → q) → (¬q → ¬p) := by
  . intro h
    apply Or.elim (em p)
    . intro hp
      . intro hnq
        exact absurd (h hp) hnq
    . intro hnp
      . intro hnq
        exact hnp
