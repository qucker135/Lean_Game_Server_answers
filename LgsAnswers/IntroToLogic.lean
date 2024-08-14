import Mathlib

-- ∧ Tutorial: Party Invites

example (P : Prop)(todo_list : P) : P := by
  exact todo_list

example (P S : Prop)(p: P)(s : S) : P ∧ S := by
  exact and_intro p s

example (A I O U : Prop)(a : A)(i : I)(o : O)(u : U) : (A ∧ I) ∧ O ∧ U := by
  have ai := and_intro a i
  have ou := and_intro o u
  exact and_intro ai ou

example (P S : Prop)(vm: P ∧ S) : P := by
  exact and_left vm

example (P Q : Prop)(h: P ∧ Q) : Q := by
  exact and_right h

example (A I O U : Prop)(h1 : A ∧ I)(h2 : O ∧ U) : A ∧ U := by
  have a := and_left h1
  have u := and_right h2
  exact and_intro a u

example (C L : Prop)(h: (L ∧ (((L ∧ C) ∧ L) ∧ L ∧ L ∧ L)) ∧ (L ∧ L) ∧ L) : C := by
  have h2: (L ∧ ((L ∧ C) ∧ L) ∧ L ∧ L ∧ L) := and_left h
  have h3: ((L ∧ C) ∧ L) ∧ L ∧ L ∧ L := and_right h2
  have h4: (L ∧ C) ∧ L := and_left h3
  have h5: L ∧ C := and_left h4
  exact and_right h5

example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  have a := h.left.right
  have c := h.right.right.left.left
  have p := h.left.left.left
  have s := h.left.left.right
  exact and_intro a (and_intro c (and_intro p s))

-- Redux: ∧ World Tactics

example (P : Prop)(h'₁ : P) : P := by
  assumption

example (P Q : Prop)(h'₁ : P)(h'₂ : Q) : P ∧ Q := by
  constructor
  assumption
  assumption

example (P Q R S : Prop)(h'₁ : P)(h'₂ : Q)(h'₃ : R)(h'₄ : S) : (P ∧ Q) ∧ R ∧ S := by
  constructor
  constructor
  assumption
  assumption
  constructor
  assumption
  assumption

example (P Q : Prop)(h: P ∧ Q) : P := by
  cases h
  assumption

example (P Q : Prop)(h: P ∧ Q) : Q := by
  cases h
  assumption

example (P Q R S : Prop)(h1 : P ∧ Q)(h2 : R ∧ S) : P ∧ S := by
  cases h1
  constructor
  assumption
  cases h2
  assumption

example (P Q : Prop)(h: (Q ∧ (((Q ∧ P) ∧ Q) ∧ Q ∧ Q ∧ Q)) ∧ (Q ∧ Q) ∧ Q) : P := by
  cases h
  cases left
  cases right_1
  cases left
  cases left_2
  assumption

example (A C I O P S U : Prop)(h: ((P ∧ S) ∧ A) ∧ ¬I ∧ (C ∧ ¬O) ∧ ¬U) : A ∧ C ∧ P ∧ S := by
  cases h
  cases right
  cases right_1
  cases left_2
  constructor
  cases left
  assumption
  constructor
  assumption
  constructor
  cases left
  cases left_2
  assumption
  cases left
  cases left_2
  assumption

-- → Tutorial: Party Snacks

example (P C: Prop)(p: P)(bakery_service : P → C) : C := by
  exact modus_ponens bakery_service p

example (C: Prop) : C → C := by
  exact fun h : C ↦ h

example (I S: Prop) : I ∧ S → S ∧ I := by
  exact fun h : (I ∧ S) ↦ and_intro h.right h.left

example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  exact fun h ↦ modus_ponens h2 (modus_ponens h1 h)

example (P Q R S T U: Prop) (p : P) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : U := by
  exact modus_ponens (imp_trans (imp_trans h1 h3) h5) p

example (C D S: Prop) (h : C ∧ D → S) : C → D → S := by
  exact fun h1 ↦
    fun h2 ↦
      have cnd := and_intro h1 h2
      modus_ponens h cnd

example (C D S: Prop) (h : C → D → S) : C ∧ D → S := by
  exact fun hx ↦
    modus_ponens (modus_ponens h hx.left) hx.right

example (C D S : Prop) (h : (S → C) ∧ (S → D)) : S → C ∧ D := by
  exact fun s ↦
    have c := modus_ponens h.left s
    have d := modus_ponens h.right s
    and_intro c d

example (R S : Prop) : R → (S → R) ∧ (¬S → R) := by
  exact fun r ↦
    and_intro (fun _ => r) (fun _ => r)

-- Redux: → World Tactics

example (P Q: Prop)(h'₁: P)(h : P → Q) : Q := by
  apply h at h'₁
  apply h'₁

example (P: Prop) : P → P := by
  intro p
  assumption

example (P Q: Prop) : P ∧ Q → Q ∧ P := by
  intro pnq
  cases pnq
  constructor
  assumption
  assumption

example (C A S: Prop) (h1 : C → A) (h2 : A → S) : C → S := by
  intro c
  apply h1 at c
  apply h2
  assumption

example (P Q R S T U: Prop) (h1 : P → Q) (h2 : Q → R) (h3 : Q → T) (h4 : S → T) (h5 : T → U) : P → U := by
  intro p
  apply h5
  apply h3
  apply h1
  assumption

example (P Q R: Prop) (h : P ∧ Q → R) : P → Q → R := by
  intro p
  intro q
  apply h
  constructor
  repeat assumption

example (P Q R: Prop) (h : P → Q → R) : P ∧ Q → R := by
  intro hpq
  apply h
  apply hpq.left
  apply hpq.right

example (P Q R : Prop) (h : (P → Q) ∧ (P → R)) : P → Q ∧ R := by
  intro p
  constructor
  apply h.left
  assumption
  apply h.right
  assumption

example (P Q : Prop) : Q → (P → Q) ∧ (¬P → Q) := by
  intro
  constructor
  repeat {intro; assumption}

-- ∨ Tutorial: The Kraken

example (O S : Prop)(s : S) : S ∨ O := by
  exact or_inl s

example (O S : Prop)(s : S) : K ∨ S := by
  exact or_inr s

example (B C I : Prop)(h1 : C → B)(h2 : I → B)(h3 : C ∨ I) : B := by
  exact or_elim h3 h1 h2

example (C O : Prop)(h : C ∨ O) : O ∨ C := by
  exact or_elim h or_inr or_inl

example (C J R : Prop)(h1 : C → J)(h2 : C ∨ R) : J ∨ R := by
  have cjr : C → (J ∨ R) := fun c => or_inl (h1 c)
  exact or_elim h2 cjr or_inr

example (G H U : Prop)(h : G ∨ H ∧ U) : (G ∨ H) ∧ (G ∨ U) := by
  have gh : G ∨ H := by
    have hugh : H ∧ U → G ∨ H := fun ⟨h, _⟩ => or_inr h
    exact or_elim h or_inl hugh
  have gu : G ∨ U := by
    have hugu : H ∧ U → G ∨ U := fun ⟨_, u⟩ => or_inr u
    exact or_elim h or_inl hugu
  exact and_intro gh gu

example (G H U : Prop)(h : G ∧ (H ∨ U)) : (G ∧ H) ∨ (G ∧ U) := by
  have ⟨g, h_or_u⟩ := h
  exact or_elim h_or_u (fun h => Or.inl ⟨g, h⟩) (fun u => Or.inr ⟨g, u⟩)

example (I K P : Prop)(h : K → P) : K ∨ I → I ∨ P := by
  have h': K → (I ∨ P) := fun k => or_inr (h k)
  exact fun k_or_i => or_elim k_or_i h' or_inl

-- ¬ Tutorial: Falsification

example : ¬False := by
  exact identity

example (B S : Prop)(h : ¬S) : S → B := by
  exact imp_trans h false_elim

example (P : Prop)(p : P) : ¬¬P := by
  exact fun np =>
    false_elim (np p)

example (L : Prop) : ¬(L ∧ ¬L) := by
  exact fun ⟨l, nl⟩ =>
    false_elim (nl l)

example (B S : Prop)(h1 : B → S)(h2 : ¬S) : ¬B := by
  exact imp_trans h1 h2

example (A : Prop) (h: A → ¬A) : ¬A := by
  exact fun a => h a a

example (B C : Prop) (h: ¬(B → C)) : ¬C := by
  exact fun c =>
    h (fun _ => c)

example (C S : Prop) (s: S) : ¬(¬S ∧ C) := by
  exact fun ⟨ns, _⟩ =>
    have false := ns s
    false_elim false

example (A P : Prop) (h : P → ¬A) : ¬(P ∧ A) := by
  exact fun ⟨p, a⟩ => h p a

example (A P : Prop) (h: ¬(P ∧ A)) : P → ¬A := by
  exact fun p =>
    fun a =>
      false_elim (h (and_intro p a))

example (A : Prop)(h : ¬¬¬A) : ¬A := by
  exact fun a =>
    h (fun na => na a)

example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  exact fun nb =>
    h (fun b => false_elim (nb b))

-- ↔ Tutorial: Party Games

example (J S : Prop) (hsj: S → J) (hjs: J → S) : S ↔ J := by
  exact iff_intro hsj hjs

example (B P : Prop) (h : B ↔ ¬P) : (B → ¬P) ∧ (¬P → B) := by
  exact ⟨h.mp, h.mpr⟩

example (P Q R : Prop) (h1 : Q ↔ R)(h2 : P → Q) : P → R := by
  exact imp_trans h2 h1.mp

example (P Q R : Prop) (h1 : P ↔ R)(h2 : P → Q) : R → Q := by
  exact imp_trans h1.mpr h2

example (A C L P : Prop) (h1 : L ↔ P) (h2 : ¬((A → C ∨ ¬P) ∧ (P ∨ A → ¬C) → (P → C)) ↔ A ∧ C ∧ ¬P) : ¬((A → C ∨ ¬L) ∧ (L ∨ A → ¬C) → (L → C)) ↔ A ∧ C ∧ ¬L := by
  rw [h1]
  exact h2

example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  rw [or_assoc, and_assoc]
  exact h

example (P Q R : Prop): (P ∧ Q ↔ R ∧ Q) ↔ Q → (P ↔ R) := by
  have h1: ((P ∧ Q ↔ R ∧ Q)) → (Q → (P ↔ R)) :=
    fun ⟨pqrq, rqpq⟩ q =>
      iff_intro (fun p => (pqrq (and_intro p q)).left) (fun r => (rqpq (and_intro r q)).left)
  have h2: (Q → (P ↔ R)) → (P ∧ Q ↔ R ∧ Q) :=
    fun h3 =>
      ⟨fun ⟨p,q⟩ => ⟨(h3 q).mp p, q⟩, fun ⟨r,q⟩ => ⟨(h3 q).mpr r, q⟩⟩
  exact iff_intro h1 h2

-- Redux: ∨ World Tactics

example (P Q : Prop)(h'₁ : P) : P ∨ Q := by
  left
  assumption

example (P Q : Prop)(h'₁ : Q) : P ∨ Q := by
  right
  assumption

example (P Q R : Prop)(h1 : Q → P)(h2 : R → P)(h3 : Q ∨ R) : P := by
  cases h3
  apply h1
  assumption
  apply h2
  assumption

example (P Q : Prop)(h : P ∨ Q) : Q ∨ P := by
  cases h
  right
  assumption
  left
  assumption

example (P Q R : Prop)(h1 : P → Q)(h2 : P ∨ R) : Q ∨ R := by
  cases h2
  left
  apply h1
  assumption
  right
  assumption

example (P Q R : Prop)(h : P ∨ Q ∧ R) : (P ∨ Q) ∧ (P ∨ R) := by
  cases h
  constructor
  left
  assumption
  left
  assumption
  constructor
  right
  cases h_1
  assumption
  right
  cases h_1
  assumption

example (P Q R : Prop)(h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  cases h
  cases right
  left
  constructor
  repeat assumption
  right
  constructor
  repeat assumption

example (P Q R : Prop)(h : Q → R) : Q ∨ P → P ∨ R := by
  intro q
  cases q
  apply h at h_1
  apply or_inr h_1
  apply or_inl h_1

-- Redux: ¬ World Tactics

example : ¬False := by
  intro
  assumption

example (P Q : Prop)(h'₁ : ¬P) : P → Q := by
  intro p
  contradiction

example (P : Prop)(h'₁ : P) : ¬¬P := by
  intro a
  apply a
  assumption

example (P : Prop) : ¬(P ∧ ¬P) := by
  intro
  cases a
  apply right at left
  assumption

example (P Q : Prop)(h1 : P → Q)(h2 : ¬Q) : ¬P := by
  intro a
  apply h1 at a
  apply h2 at a
  assumption

example (P : Prop) (h: P → ¬P) : ¬P := by
  intro p
  apply h
  repeat assumption

example (P Q : Prop) (h: ¬(P → Q)) : ¬Q := by
  intro q
  apply h
  intro p
  assumption

example (P Q : Prop) (h: Q) : ¬(¬Q ∧ P) := by
  intro a
  cases a
  apply left
  assumption

example (P Q : Prop) (h : Q → ¬P) : ¬(Q ∧ P) := by
  intro a
  cases a
  apply h
  repeat assumption

example (P Q : Prop) (h: ¬(Q ∧ P)) : Q → ¬P := by
  intro q p
  apply h
  apply and_intro q p

example (P : Prop)(h : ¬¬¬P) : ¬P := by
  intro a
  apply h
  intro b
  apply b
  assumption

example (B C : Prop) (h : ¬(B → C)) : ¬¬B := by
  intro nb
  apply h
  intro b
  contradiction

-- Redux: ↔ World Tactics

example (P Q : Prop) (hsj: Q → P) (hjs: P → Q) : Q ↔ P := by
  constructor
  repeat assumption

example (P Q : Prop) (h : P ↔ ¬Q) : (P → ¬Q) ∧ (¬Q → P) := by
  cases h
  constructor
  repeat assumption

example (P Q R : Prop) (h1 : Q ↔ R)(h2 : P → Q) : P → R := by
  intro h
  apply h1.mp
  apply h2
  assumption

example (P Q R : Prop) (h1 : P ↔ R)(h2 : P → Q) : R → Q := by
  intro h
  apply h2
  apply h1.mpr
  assumption

example (P Q R S : Prop) (h1 : R ↔ S) (h2 : ¬((P → Q ∨ ¬S) ∧ (S ∨ P → ¬Q) → (S → Q)) ↔ P ∧ Q ∧ ¬S) : ¬((P → Q ∨ ¬R) ∧ (R ∨ P → ¬Q) → (R → Q)) ↔ P ∧ Q ∧ ¬R := by
  apply Iff.intro
    (
      λh₃ ↦ h2.mp (
        λh₄ ↦ h₃ (λ⟨hl₅,hr₅⟩ l ↦ h₄ ⟨
          λa ↦ or_elim
            (hl₅ a)
            or_inl
            (imp_trans h1.mpr ≫ or_inr)
        ,
          λ_ ↦ hr₅ (or_inl l)
        ⟩ (h1.mp l))
      ) |> (λ ⟨a, c, np⟩ ↦ ⟨a, c, h1.mp ≫ np⟩)
    )
    (
      λ⟨a,c,nl⟩ _ ↦ false_elim (
        h2.mpr
          ⟨a, c, h1.mpr ≫ nl⟩
          λ_ _ ↦ c
      )
    )

example (P Q R : Prop) (h : P ∨ Q ∨ R → ¬(P ∧ Q ∧ R)) : (P ∨ Q) ∨ R → ¬((P ∧ Q) ∧ R) := by
  apply or_assoc.mp ≫ h ≫ imp_trans and_assoc.mp

example (P Q R : Prop): (P ∧ Q ↔ R ∧ Q) ↔ Q → (P ↔ R) := by
  constructor
  intro h q
  constructor
  cases h
  intro p
  have pq := and_intro p q
  apply mp at pq
  exact pq.left
  intro r
  cases h
  have rq := and_intro r q
  apply mpr at rq
  exact rq.left
  intro h
  constructor
  intro h1
  cases h1
  have q := right
  apply h at right
  cases right
  apply mp at left
  exact and_intro left q
  intro rq
  cases rq
  have q := right
  apply h at right
  constructor
  cases right
  apply mpr at left
  exact left
  exact q
