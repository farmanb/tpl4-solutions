-- try it 
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

example : (∃ x : α, r) → r := 
  (fun h : (∃ x : α, r) =>
    Exists.elim h
      (fun x => 
        (fun hr : r => hr)
      )
  )
example (a : α) : r → (∃ x : α, r) := 
  (fun hr : r =>
    Exists.intro a hr
  )

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
  Iff.intro
    (fun h : (∃ x, p x ∧ r) =>
      Exists.elim h
        (fun x =>
          (fun hx : p x ∧ r =>
            And.intro (Exists.intro x (And.left hx)) (And.right hx)
          )
        )
    )
    (fun h : (∃ x, p x) ∧ r => 
      Exists.elim (And.left h)
        (fun x =>
          (fun hx : p x =>
            Exists.intro x (And.intro hx (And.right h))
          )
        )
    )

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
