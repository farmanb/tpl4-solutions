-- try it 
variable (p q r : Prop)

#check And.intro
#check Iff.intro
#check And.left

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
Iff.intro
(fun h₁ : p ∧ q => And.intro (And.right h₁) (And.left h₁))
(fun h₂ : q ∧ p => And.intro (And.right h₂) (And.left h₂))

#check Or.elim
#check Or.intro_right  

example : p ∨ q ↔ q ∨ p := 
Iff.intro
  (fun h : p ∨ q => Or.elim h
  (fun hp : p => Or.intro_right q hp)
  (fun hq : q => Or.intro_left p hq))
  (fun h : q ∨ p => Or.elim h
  (fun hq : q => Or.intro_right p hq)
  (fun hp : p => Or.intro_left q hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
  Iff.intro
  (fun h : (p ∧ q) ∧ r => 
    And.intro 
      (And.left (And.left h))
      (And.intro (And.right (And.left h)) (And.right h)))
  (fun (h : p ∧ (q ∧ r)) => 
    And.intro 
      (And.intro (And.left h) (And.left (And.right h))) 
      (And.right (And.right h)))

#check Or.elim

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
        (fun hpq : (p ∨ q) => 
          Or.elim hpq
            (fun hp : p => 
              Or.intro_left (q ∨ r) hp)
            (fun hq : q => 
              Or.intro_right p (Or.intro_left r hq)
            )
        )
        (fun hr : r => 
          Or.intro_right p (Or.intro_right q hr)
        )
    )
    (fun h : p ∨ (q ∨ r) => 
      Or.elim h
        (fun hp : p => 
          Or.intro_left r (Or.intro_left q hp)
        )
        (fun hqr : q ∨ r => 
          Or.elim hqr
            (fun hq : q => 
              Or.intro_left r (Or.intro_right p hq)
            )
            (fun hr : r => Or.intro_right (p ∨ q) hr)
        )
    )
-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun h : p ∧ (q ∨ r) => 
      have hp : p := (And.left h)
      Or.elim (And.right h)
        (fun hq : q => 
          Or.intro_left (p ∧ r) (And.intro hp hq)
        )
        (fun hr : r => 
          Or.intro_right (p ∧ q) (And.intro hp hr)
        )
    )
    (fun h : (p ∧ q) ∨ (p ∧ r) => 
      Or.elim h
        (fun hpq : p ∧ q => And.intro 
          (And.left hpq)
          (Or.intro_left r (And.right hpq))
        )
        (fun hpr : p ∧ r => And.intro
          (And.left hpr)
          (Or.intro_right q (And.right hpr))
        )
    )

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
  (fun h : p ∨ (q ∧ r) => 
    Or.elim h
      (fun hp : p => 
        And.intro
          (Or.intro_left q hp)
          (Or.intro_left r hp)
      )
      (fun hqr : q ∧ r => 
        And.intro
          (Or.intro_right p (And.left hqr))
          (Or.intro_right p (And.right hqr))
      )
  )
  (fun h : (p ∨ q) ∧ (p ∨ r) => 
    Or.elim (And.left h)
      (fun hp : p => Or.intro_left (q ∧ r) hp)
      (fun hq : q => 
        Or.elim (And.right h)
          (fun hp : p => Or.intro_left (q ∧ r) hp)
          (fun hr : r => Or.intro_right p (And.intro hq hr))
      )
  )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
    (fun h : (p → (q → r)) => (fun hpq : p ∧ q => h (And.left hpq) (And.right hpq)))
    (fun h : (p ∧ q → r ) => (fun hp : p => (fun hq : q => h (And.intro hp hq))))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
  Iff.intro
    (fun h : (p ∨ q) → r => And.intro
      (fun hp : p => h (Or.intro_left q hp))
      (fun hq : q => h (Or.intro_right p hq))
    )
    (fun h : (p → r) ∧ (q → r) => 
      (fun hpq : p ∨ q => 
        Or.elim hpq
          (fun hp : p => (And.left h) hp)
          (fun hq : q => (And.right h) hq)
      )
    )

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
    (fun h : ¬(p ∨ q) => 
      And.intro 
        (fun hp : p => False.elim (h (Or.intro_left q hp))) 
        (fun hq : q => False.elim (h (Or.intro_right p hq)))
    )
    (fun h : ¬p ∧ ¬ q => 
      (fun hpq : p ∨ q => 
        Or.elim hpq
          (fun hp : p => False.elim ((And.left h) hp))
          (fun hq : q => False.elim ((And.right h) hq))
      )
    )
example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  (fun h : ¬p ∨ ¬q => 
    (fun hpq : p ∧ q => Or.elim h
      (fun hnp : ¬p => absurd (And.left hpq) hnp)
      (fun hnq : ¬q => absurd (And.right hpq) hnq)
    )
  )
example : ¬(p ∧ ¬p) := 
  (fun h : p ∧ ¬p => absurd (And.left h) (And.right h))

example : p ∧ ¬q → ¬(p → q) := 
  (fun h₁ : p ∧ ¬q =>
    (fun h₂ : p → q =>
      absurd (h₂ (And.left h₁)) (And.right h₁)
    )
  )

#check absurd
example : ¬p → (p → q) := 
  (fun hnp : ¬p =>
    (fun hp : p =>
      show q from absurd hp hnp
    )
  )

example : (¬p ∨ q) → (p → q) := 
  (fun hnpq : ¬p ∨ q =>
    (fun hp : p => 
      Or.elim hnpq
        (fun hnp : ¬p => show q from absurd hp hnp)
        (fun hq : q => hq)
    )
  )
example : p ∨ False ↔ p := 
  Iff.intro
    (fun h : p ∨ False => 
      Or.elim h
        (fun hp : p => hp)
        (fun hf : False => False.elim hf)
    )
    (fun h : p =>
      Or.intro_left False h
    )

example : p ∧ False ↔ False := 
  Iff.intro
    (fun h : p ∧ False =>
      And.right h
    )
    (fun h : False => 
      False.elim h
    )
example : (p → q) → (¬q → ¬p) := 
  (fun hpq : p → q =>
    (fun hnq : ¬ q =>
      (fun hp : p =>
        absurd (hpq hp) hnq
      )
    )
  )

  open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := 
  (fun h : p → q ∨ r =>
    Or.elim (em p)
      (fun hp : p => 
        Or.elim (h hp)
          (fun hq : q => Or.intro_left (p → r) (fun p => hq))
          (fun hr : r => Or.intro_right (p → q) (fun p => hr))
      )
      (fun hnp : ¬p => 
        Or.intro_left (p → r) (fun hp : p => absurd hp hnp)
      )
  )

example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  (fun h : ¬(p ∧ q) =>
    (Or.elim (em p)
      (fun hp : p => 
        Or.elim (em q)
          (fun hq : q => absurd (And.intro hp hq) h)
          (fun hnq : ¬q => Or.intro_right (¬p) hnq)
      )
      (fun hnp : ¬p => Or.intro_left (¬ q) hnp)
    )
  )

example : ¬(p → q) → p ∧ ¬q := 
  (fun h : ¬(p → q) =>
    Or.elim (em p)
      (fun hp : p => 
        have hnq : ¬q :=
          (fun hq : q => 
            have hpq : p → q := (fun p => hq)
            False.elim (h hpq)
          )
        And.intro
          hp
          hnq -- Proof of ¬q
      ) 
      (fun hnp : ¬p => 
        have hpq : p → q :=
          (fun hp : p => False.elim (hnp hp))
        False.elim (h hpq)
      )
  )

example : (p → q) → (¬p ∨ q) := 
  (fun h : p → q =>
    Or.elim (em p)
      (fun hp : p => Or.intro_right (¬p) (h hp))
      (fun hnp : ¬p => Or.intro_left q hnp)
  )

example : (¬q → ¬p) → (p → q) := 
  (fun h : ¬q → ¬p => 
    Or.elim (em q)
      (fun hq : q => (fun p => hq))
      (fun hnq : ¬q => 
        have hnp : ¬p := h hnq
        (fun hp : p => show q from absurd hp hnp)
      )
  )
example : p ∨ ¬p := 
  Or.elim (em p)
    (fun hp : p => Or.intro_left (¬p) hp)
    (fun hnp : ¬p => Or.intro_right p hnp)

example : (((p → q) → p) → p) := 
  (fun h : (p → q) → p => 
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => 
        have hpq : p → q :=
          (fun hp : p => show q from absurd hp hnp)
        h hpq
      )
  )


example : ¬(p ↔ ¬p) :=
  (fun h : p ↔ ¬ p =>
    /- Prove that ¬P is true-/
    have hnp : ¬p := (fun hp : p => absurd hp (h.mp hp))

    /- Use this to prove P is true-/
    have hp : p := h.mpr hnp

    /- Now we have arrived at a contradiction. -/
    False.elim (hnp hp)
  )