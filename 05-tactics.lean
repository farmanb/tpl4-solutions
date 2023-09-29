-- try it 
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro <;> intro
    | ⟨h₁,h₂⟩ => exact ⟨h₂,h₁⟩

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro <;> intro
    | Or.inl h => apply Or.inr h;
    | Or.inr h => apply Or.inl h;

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro 
    | ⟨h₁,h₂⟩ => exact And.intro h₁.left (And.intro h₁.right h₂)
  . intro
    | ⟨h₁,h₂⟩ => exact And.intro (And.intro h₁ h₂.left) h₂.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro
    | Or.inl hpq => cases hpq with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | Or.inr hr => exact Or.inr (Or.inr hr)
  . intro
    | Or.inl hp => exact Or.inl (Or.inl hp)
    | Or.inr hqr => cases hqr with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr
    
-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, hqr⟩ => cases hqr with
      | inl hq => exact Or.inl (And.intro hp hq)
      | inr hr => exact Or.inr (And.intro hp hr)
  . intro
    | Or.inl hpq => exact And.intro hpq.left (Or.inl hpq.right);
    | Or.inr hpr => exact And.intro hpr.left (Or.inr hpr.right);

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  intro h;
  cases h with
  | inl hp => apply And.intro <;> exact Or.inl hp;
  | inr hqr => apply And.intro <;> apply Or.inr; exact hqr.left ; exact hqr.right

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h₁ h₂
    exact h₁ (h₂.left) h₂.right
  . intro h₁ h₂ h₃ 
    exact h₁ (And.intro h₂ h₃)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    apply And.intro
    intro hp
    exact h (Or.inl hp)
    intro hq
    exact h (Or.inr hq)
  . intro
    | ⟨hpr,hpq⟩ => intro 
      | Or.inl hp => exact hpr hp
      | Or.inr hp => exact hpq hp

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply And.intro
    intro hp
    exact h (Or.inl hp)
    intro hq
    exact h (Or.inr hq)
  . intro ⟨hnp,hnq⟩
    intro
    | Or.inl hp => exact hnp hp;
    | Or.inr hq => exact hnq hq;

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro
  | Or.inl hnp => intro ⟨hp,_⟩; exact hnp hp
  | Or.inr hnq => intro ⟨_,hq⟩; exact hnq hq
  
example : ¬(p ∧ ¬p) := by
  intro 
  | ⟨hp,hnp⟩ => exact hnp hp
  

example : p ∧ ¬q → ¬(p → q) := by
  intro 
  | ⟨hp, hnq⟩ => intro
    | hpq => apply hnq; exact hpq hp
  

example : ¬p → (p → q) := by
  intro
  | hnp => intro
    | hp => exact False.elim (hnp hp)
  

example : (¬p ∨ q) → (p → q) := by
  intro
  | Or.inl hnp => intro
    | hp => exact False.elim (hnp hp)
  | Or.inr hq => intro
    | _ => exact hq;

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro
    | Or.inl hp => exact hp
    | Or.inr hf => exact False.elim (hf)
  . intro
    | hp => exact Or.inl hp

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro
    | ⟨_,hf⟩ => exact hf;
  . intro
    | hf => exact False.elim hf
  
example : (p → q) → (¬q → ¬p) := by
  intro hpq hnp hp
  exact hnp (hpq hp)

  open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases (Classical.em p) with 
  | inl hp => cases h hp with
    | inl hq => apply Or.inl; intro; exact hq
    | inr hr => apply Or.inr; intro; exact hr
  | inr hnp => apply Or.inl; intro hp; apply False.elim; apply hnp; exact hp

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (Classical.em p) with
  | inl hp => apply Or.inr; intro hq; apply h; apply And.intro; exact hp; exact hq
  | inr hnp => apply Or.inl; intro hp; apply hnp; exact hp

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  cases (Classical.em p) with
  | inl hp => apply And.intro; exact hp; intro hq; apply h; exact (fun hp => hq)
  | inr hnp => apply And.intro; apply False.elim; apply h; intro hp; apply False.elim; apply hnp; exact hp; intro hq; apply h; exact (fun _ => hq)

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (Classical.em p) with
  | inl hp => apply Or.inr; exact h hp;
  | inr hnp => apply Or.inl; exact hnp;

example : (¬q → ¬p) → (p → q) := by
  intro h hp;
  cases (Classical.em q) with
  | inl hq => exact hq;
  | inr hnq => apply False.elim; exact h hnq hp;

example : p ∨ ¬p := by
  cases (Classical.em p) with
  | inl hp => apply Or.inl; exact hp;
  | inr hnp => apply Or.inr; exact hnp;

example : (((p → q) → p) → p) := by
  intro h
  cases (Classical.em p) with
  | inl hp => exact hp;
  | inr hnp => apply h; intro hp; apply False.elim; apply hnp; exact hp;

example : ¬(p ↔ ¬p) := by
  intro h
  have hnp : ¬p := (fun hp : p => absurd hp (h.mp hp))
  apply hnp;
  exact h.mpr hnp;

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    apply And.intro
    intro x; exact (h x).left;
    intro x; exact (h x).right;
  . intro h
    intro x
    exact And.intro (h.left x) (h.right x)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h₁ h₂ x
  exact (h₁ x) (h₂ x) 
  
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl hupx => apply Or.inl (hupx x)
  | inr huqx => apply Or.inr (huqx x)

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro x
  apply Iff.intro
  . intro h
    exact (h x)
  . intro h _
    exact h
  
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    cases (Classical.em r) with
    | inl hr => apply Or.inr; exact hr;
    | inr hnr => apply Or.inl; intro x; cases (h x) with
      | inl hp => exact hp;
      | inr hr => apply False.elim; apply hnr; exact hr
  . intro h
    intro x
    cases h with
    | inl hupx => apply Or.inl; exact (hupx x)
    | inr hr => apply Or.inr; exact hr

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h₁ h₂ x
    exact ((h₁ x) h₂);
  . intro h₁ x h₂
    apply h₁
    exact h₂


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
  . intro h
    cases h with
    | intro x hpxr => apply And.intro; exact ⟨x,hpxr.left⟩; exact hpxr.right
  . intro h
    cases h with
    |intro hepx hr => cases hepx with
    | intro x hpx => exact ⟨x, And.intro hpx hr⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro
    | ⟨x, Or.inl h⟩ => apply Or.inl; exact ⟨x,h⟩
    | ⟨x, Or.inr h⟩ => apply Or.inr; exact ⟨x,h⟩  
  . intro
    | Or.inl ⟨x,h⟩ => exact ⟨x, Or.inl h⟩
    | Or.inr ⟨x,h⟩=> exact ⟨x, Or.inr h⟩ 

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    intro ⟨x, hnpx⟩
    apply hnpx
    exact h x
  . intro h x
    apply Classical.byContradiction
    intro hnpx
    apply h
    exact ⟨x,hnpx⟩
    
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro ⟨x, hpx⟩
    intro hunpx
    apply hunpx x
    exact hpx
  . intro hnunpx
    apply Classical.byContradiction
    intro hnepx
    apply hnunpx
    intro x
    intro hpx
    apply hnepx
    exact ⟨x,hpx⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro hnepx
    intro x hpx
    apply hnepx
    exact ⟨x,hpx⟩
  . intro hunpx
    intro ⟨x,hpx⟩
    apply hunpx x
    exact hpx


example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro hnupx
    apply Classical.byContradiction
    intro hnenpx
    apply hnupx
    intro x
    cases Classical.em (p x) with
    | inl hp => exact hp
    | inr hnp => apply False.elim; apply hnenpx; exact ⟨x,hnp⟩
  . intro ⟨x, hnpx⟩
    intro hupx
    apply hnpx
    exact hupx x

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro hupxr
    intro ⟨x,hpx⟩ 
    exact (hupxr x) hpx
  . intro h
    intro x hpx
    exact h ⟨x, hpx⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro ⟨x,hpxr⟩
    intro hupx
    apply hpxr
    exact hupx x
  . intro h
    cases Classical.em (∀ x, p x) with
    | inl hupx => exact ⟨a, (fun hpa : p a => h hupx)⟩ 
    | inr hnupx => apply Classical.byContradiction; intro hnepxr; apply hnupx; intro x; apply Classical.byContradiction; intro hnpx; apply hnepxr; exact ⟨x, (fun hpx : p x => absurd hpx hnpx)⟩


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro ⟨x,hrpx⟩
    intro hr
    exact ⟨x, (hrpx hr)⟩
  . intro h
    cases (Classical.em r) with 
    | inl hr => cases (h hr) with
      | intro x hpx => exists x; intro _; exact hpx
    | inr hnr => exists a; intro hr; apply False.elim; apply hnr; exact hr
    
 
-- try it 
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  specialize h barber
  apply h.mp;
  apply h.mpr;
  intro h';
  apply h.mp;
  exact h';
  exact h';
  apply h.mpr;
  intro h'
  apply h.mp;
  exact h';
  exact h';


example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
        constructor; apply Or.inl; assumption; constructor <;> apply Or.inr; apply Or.inl; assumption; apply Or.inr; assumption

        

