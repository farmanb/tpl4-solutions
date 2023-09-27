-- try it 
variable (p q r : Prop)

#check And.intro
#check Iff.intro
#check And.left

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  intro h
  exact (And.intro (And.right h) (And.left h))
  intro h
  exact (And.intro (And.right h) (And.left h))

#check Or.elim
#check Or.intro_right  

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  intro h
  cases h
  apply Or.intro_right
  assumption
  apply Or.intro_left
  assumption

  intro h
  cases h
  apply Or.intro_right
  assumption
  apply Or.intro_left
  assumption

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

  variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro
    (fun h : (∀ x, p x ∧ q x) => 
      And.intro
      (fun x => show p x from (h x).left)
      (fun x => show q x from (h x).right)
    )
    (fun h : (∀ x, p x) ∧ (∀ x, q x) => 
      (fun x => And.intro (h.left x) (h.right x))
    )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
  (fun h : ∀ x, p x → q x =>
    (fun h' : ∀ x, p x =>
      (fun x => h x (h' x))
    )
  )
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  (fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    (fun x => 
      Or.elim h
        (fun hp : (∀ x, p x) => Or.intro_left (q x) (hp x))
        (fun hq : (∀ x, q x) => Or.intro_right (p x) (hq x)))
  )

-- try it 
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := 
  (fun x : α => 
    Iff.intro
      (fun h : (∀ x : α, r) => h x)
      (fun h : r => (fun α => h))
  )
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
  Iff.intro
    (fun h : (∀ x, p x ∨ r) => 
      Or.elim (Classical.em (r))
        (fun hr : r => Or.intro_right (∀ x, p x) hr)
        (fun hnr : ¬r => 
          Or.intro_left 
            r 
            (fun x => 
              Or.elim (h x)
                (fun hpx : p x => hpx)
                (fun hr : r => absurd hr hnr) -- Case can't happen: can't have r and ¬r.
            )
        )
    )
    (fun h : (∀ x, p x) ∨ r => 
      (fun x => Or.elim h
        (fun hl : (∀ x, p x) => Or.intro_left r (hl x))
        (fun hr : r => Or.intro_right (p x) hr)
      )
    )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
  Iff.intro
  (fun h : (∀ x, r → p x) => 
    (fun hr : r =>
      (fun x => (h x) hr))
  )
  (fun h : r → (∀ x, p x) => 
    (fun x => (fun hr : r => (h hr) x))
  )

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro
  | ⟨_,hr⟩ => exact hr

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a,hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  intro h
  cases h with
  | intro x hpxr => apply And.intro; exact ⟨x,hpxr.left⟩; exact hpxr.right

  intro h
  cases h with
  |intro hepx hr => cases hepx with
  | intro x hpx => exact ⟨x, And.intro hpx hr⟩
 

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := 
  Iff.intro
    (fun h : (∃ x, p x ∨ q x) => 
      Exists.elim h
      (fun x =>
        (fun hx : p x ∨ q x =>
          Or.elim hx
          (fun hpx : p x => 
            Or.intro_left (∃ x, q x) (Exists.intro x hpx)
          )
          (fun hqx : q x => 
            Or.intro_right (∃ x, p x) (Exists.intro x hqx)
          )
        )
      )
    )
    (fun h : (∃ x, p x) ∨ (∃ x, q x) => 
      Or.elim h
        (fun h₁ : (∃ x, p x) => 
          Exists.elim h₁
            (fun x => 
              (fun hpx : p x => Exists.intro x (Or.intro_left (q x) hpx))
            )
          )
        (fun h₂ : (∃ x, q x) => 
          Exists.elim h₂
            (fun x =>
              (fun hqx : q x => Exists.intro x (Or.intro_right (p x) hqx))
            )
        )
    )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
  Iff.intro
    (fun h : (∀ x, p x) => 
      (fun h₂ : ∃ x, ¬ p x => 
        Exists.elim h₂
        (fun x => 
          (fun hnpx : ¬p x => 
            absurd (h x) hnpx
          )
        )
      )
    )
    (fun h : ¬ (∃ x, ¬p x) => 
      (fun x => 
        Or.elim (Classical.em (p x))
          (fun hp : p x => hp)
          (fun hnp : ¬p x => 
            False.elim (h (Exists.intro x hnp))
          )
      )
    )

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
  Iff.intro 
    (fun h : (∃ x, p x) => 
      (fun h' : (∀ x, ¬ p x) => 
        Exists.elim h
        (fun x =>
          (fun hpx : p x =>
            have hnpx : ¬ p x := h' x
            absurd hpx hnpx
          )
        )
      )
    )
    (fun h : ¬ (∀ x, ¬ p x) => 
      Classical.byContradiction
        (fun h₁ : ¬(∃ x, p x) =>
          have h₂ : (∀ x, ¬ p x) := 
            (fun x => 
              Or.elim (Classical.em (p x))
              (fun hp : p x => 
                have hepx : (∃ x, p x) := Exists.intro x hp
                absurd hepx h₁
              )
              (fun hnp : ¬p x => hnp)
            )
          False.elim (h h₂)
        )
    )

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
  Iff.intro
    (fun h : (¬ ∃ x, p x) => 
      (fun x =>
        (fun hpx : p x => -- Prove ∀ x, (p x → False), which is definitionally ∀ x, ¬p x.
          have hepx : ∃ x, p x := Exists.intro x hpx
          False.elim (h hepx)
        )
      )
    )
    (fun h : (∀ x, ¬ p x) => -- To prove ¬ (∃ x, p x), prove (∃ x, p x) -> False.
      (fun hex : ∃ x, p x =>
        Exists.elim hex
        (fun x => 
          (fun hpx : p x =>
            False.elim ((h x) hpx)
          )
        )
      )
    )


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := 
  Iff.intro
    (fun h : (¬ ∀ x, p x) => 
      Classical.byContradiction
      (fun h₁ : ¬(∃ x, ¬ p x) =>
        have h₂ : ∀ x, p x :=
          (fun x =>
            Or.elim (Classical.em (p x))
            (fun hpx : p x => 
              hpx
            )
            (fun hnpx : ¬p x => 
              absurd (Exists.intro x hnpx) h₁
            )
          )
        False.elim (h h₂)
      )
    )
    (fun h : (∃ x, ¬ p x) =>
      (fun h₁ : ∀ x, p x =>
        Exists.elim h
        (fun x => 
          (fun hnpx : ¬ p x =>
            have hpx : p x := h₁ x
            absurd hpx hnpx
          )
        )
      )
    )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
  Iff.intro
    (fun h : (∀ x, p x → r) => 
      (fun h₁ : (∃ x, p x) => 
        Exists.elim h₁
        (fun x =>
          (fun hpx : p x => (h x) hpx)
        )
      )
    )
    (fun h : (∃ x, p x) → r =>
      (fun x =>
        (fun hp : p x =>
          h (Exists.intro x hp)
        )
      )
    )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
  Iff.intro
    (fun h : (∃ x, p x → r) =>
      (fun hpx : (∀ x, p x) => -- Assume ∀ x, p x
        Exists.elim h -- Produce x that satisfies p x → r
          (fun x =>
            (fun hpxr : p x →r =>
              hpxr (hpx x) -- Conclude r because p x.
            )
          )
      )
    )
    (fun h : (∀ x, p x) → r => 
      show (∃ x, p x → r) from
      Classical.byCases
      (fun hp : (∀ x, p x) => 
        Exists.intro a (fun _ => (h hp))
      )
      (fun hnupx: ¬(∀ x, p x) => 
        Classical.byContradiction
        (fun hnepxr : ¬ (∃ x, p x →r ) =>
          have hupx : (∀ x, p x) :=
            (fun x =>
              Classical.byContradiction
              (fun hnpx : ¬ p x =>
                have hepxr : ∃ x, p x →r := 
                  Exists.intro x (fun hpx : p x => absurd hpx hnpx)
                show False from hnepxr hepxr
              )
            )
          show False from hnupx hupx
        )
      )
    )
    
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
  Iff.intro
    (fun h : (∃ x, r → p x) => 
      (fun hr : r => 
        Exists.elim h
          (fun x => 
            (fun hrpx : r → p x =>
              Exists.intro x (hrpx hr)
            )
          )
      )
    )
    (fun h : r → (∃ x, p x) => -- r → (∃ x, p x) ↔ ¬r ∨ (∃ x, p x) 
      Or.elim (Classical.em r)
        (fun hr : r => 
          Exists.elim (h hr) -- Use r to produce x satisfying p x.
            (fun x => 
              (fun hpx : p x => 
                Exists.intro x (fun h' : r => hpx) -- Cook up r → px.
              )
            )
        )
        (fun hnr : ¬r => Exists.intro a (fun hr : r => False.elim (hnr hr)))
    )
    
 
-- try it 
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
  have h₁ : shaves barber barber ↔ ¬ shaves barber barber := h barber
  have h₂ : ¬ shaves barber barber :=
    (fun h₃ : shaves barber barber => 
      have h₄ : ¬ shaves barber barber :=
        h₁.mp h₃
      show False from absurd h₃ h₄
    )
  have h₃ : shaves barber barber := h₁.mpr h₂
  False.elim (h₂ h₃)

-- try it 
def divides (m n : Nat) : Prop := ∃ (k : Nat), n = k*m

def even (n : Nat) : Prop := divides 2 n

def composite (n : Nat) : Prop := ∃ (k : Nat), 1 < k ∧ k < n ∧ divides k n

def prime (n : Nat) : Prop := ¬composite n

def infinitely_many_primes : Prop := ∀ n : Nat, ∃ p : Nat, prime p ∧ n < p

def Fermat_number (n : Nat) : Prop := ∃ k : Nat, n = 2^(2^k) + 1

def Fermat_prime (n : Nat) : Prop := Fermat_number n ∧ prime n  

def infinitely_many_Fermat_primes : Prop := ∀ n : Nat, ∃ p : Nat, Fermat_prime p ∧ n < p

def goldbach_conjecture : Prop := ∀ n, n > 2 → ∃ p q, p + q = n ∧ prime p ∧ prime q

def Goldbach's_weak_conjecture : Prop := ∀ n, even n ∧ n > 5 → ∃ p p' p'', p + p' + p'' = n ∧ prime p ∧ prime p' ∧ prime p''

def Fermat's_last_theorem : Prop := ∀ n, n > 2 → ¬∃ a b c, a^n + b^n = c^n ∧ a > 0 ∧ b > 0 ∧ c > 0
