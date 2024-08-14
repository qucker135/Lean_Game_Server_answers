import Mathlib

-- Subset World

example (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  exact h2 (h1 h3)

example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  intro h
  exact h2 (h1 h)

theorem Subset.refl (A : Set U) : A ⊆ A := by
  intro x
  intro h
  exact h

theorem Subset.trans {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x
  intro h
  exact h2 (h1 h)

-- Complement World

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra h
  have h3 := h h1
  exact h2 h3

theorem mem_compl_iff (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl

theorem compl_subset_compl_of_subset {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x
  intro h
  rw [mem_compl_iff]
  rw [mem_compl_iff] at h
  by_contra h2
  have h3 := h1 h2
  exact h h3

theorem compl_compl (A : Set U) : Aᶜᶜ = A := by
  apply Subset.antisymm
  intro x
  intro h
  rw [mem_compl_iff] at h
  rw [mem_compl_iff] at h
  push_neg at h
  exact h
  intro x
  intro h
  rw [mem_compl_iff]
  rw [mem_compl_iff]
  push_neg
  exact h

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  constructor
  intro h
  intro x
  intro h1
  rw [mem_compl_iff] at h1
  rw [mem_compl_iff]
  by_contra
  apply h at a
  exact h1 a
  intro h
  intro x
  intro h1
  apply compl_subset_compl_of_subset at h
  rw [compl_compl, compl_compl] at h
  apply h h1

-- Intersection World

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  rw [mem_inter_iff] at h
  exact h.right

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x
  intro h
  rw [mem_inter_iff] at h
  exact h.left

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  apply And.intro h1 h2

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x
  intro h
  have hd := h
  apply h1 at h
  apply h2 at hd
  exact And.intro h hd

theorem inter_subset_swap (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x
  intro h
  rw [mem_inter_iff] at h
  rw [mem_inter_iff]
  constructor
  exact h.right
  exact h.left

theorem inter_comm (A B : Set U) : A ∩ B = B ∩ A := by
  apply Subset.antisymm
  apply inter_subset_swap
  apply inter_subset_swap

theorem inter_assoc (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  constructor
  intro h
  rw [mem_inter_iff, mem_inter_iff]
  rw [mem_inter_iff, mem_inter_iff] at h
  constructor
  exact h.1.1
  constructor
  exact h.1.2
  exact h.2
  intro h
  rw [mem_inter_iff, mem_inter_iff]
  rw [mem_inter_iff, mem_inter_iff] at h
  constructor
  constructor
  exact h.1
  exact h.2.1
  exact h.2.2

-- Union World

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

example (A B : Set U) : B ⊆ A ∪ B := by
  intro x h
  rw [mem_union]
  exact Or.inr h

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x h3
  rw [mem_union] at h3
  cases' h3 with h3A h3B
  apply h1 at h3A
  exact h3A
  apply h2 at h3B
  exact h3B

theorem union_subset_swap (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x h
  rw [mem_union]
  rw [mem_union] at h
  cases' h with ha hb
  exact Or.inr ha
  exact Or.inl hb

theorem union_comm (A B : Set U) : A ∪ B = B ∪ A := by
  apply Subset.antisymm
  apply union_subset_swap
  apply union_subset_swap

theorem union_assoc (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  constructor
  intro h
  cases' h with ha hb
  cases' ha with ha1 ha2
  rw [mem_union, mem_union]
  apply Or.inl ha1
  rw [mem_union, mem_union]
  right
  apply Or.inl ha2
  rw [mem_union, mem_union]
  right
  apply Or.inr hb
  intro h
  cases' h with h1 h2
  rw [mem_union, mem_union]
  left
  apply Or.inl h1
  rw [mem_union, mem_union]
  rw [mem_union] at h2
  cases' h2 with h2a h2b
  left
  apply Or.inr h2a
  right
  exact h2b

-- Combination World

theorem compl_union (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  apply Subset.antisymm
  intro x h
  rw [mem_inter_iff]
  rw [mem_compl_iff] at h
  rw [mem_compl_iff, mem_compl_iff]
  rw [mem_union] at h
  constructor
  by_contra ha
  have haorb : x ∈ A ∨ x ∈ B := Or.inl ha
  exact h haorb
  by_contra hb
  have haorb : x ∈ A ∨ x ∈ B := Or.inr hb
  exact h haorb
  intro x h
  rw [mem_inter_iff] at h
  rw [mem_compl_iff, mem_compl_iff] at h
  rw [mem_compl_iff]
  rw [mem_union]
  by_contra hx
  cases' hx with hx1 hx2
  exact h.left hx1
  exact h.right hx2

theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw [← compl_compl (Aᶜ ∪ Bᶜ)]
  rw [compl_union]
  rw [compl_compl, compl_compl]

theorem inter_distrib_left (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply Subset.antisymm
  intro x h
  rw [mem_inter_iff, mem_union] at h
  rw [mem_union, mem_inter_iff, mem_inter_iff]
  cases' h with h1 h2
  cases' h2 with h2a h2b
  exact Or.inl (And.intro h1 h2a)
  exact Or.inr (And.intro h1 h2b)
  intro x h
  rw [mem_union, mem_inter_iff, mem_inter_iff] at h
  rw [mem_inter_iff, mem_union]
  cases' h with h1 h2
  constructor
  exact h1.left
  exact Or.inl h1.right
  constructor
  exact h2.left
  exact Or.inr h2.right

theorem union_distrib_left (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply Subset.antisymm
  intro x h
  rw [mem_inter_iff, mem_union, mem_union]
  rw [mem_union, mem_inter_iff] at h
  cases' h with h1 h2
  constructor
  exact Or.inl h1
  exact Or.inl h1
  constructor
  exact Or.inr h2.left
  exact Or.inr h2.right
  intro x h
  rw [mem_inter_iff, mem_union, mem_union] at h
  rw [mem_union, mem_inter_iff]
  cases' h with h1 h2
  cases' h1 with h1a
  exact Or.inl h1a
  cases' h2 with h2a h2b
  exact Or.inl h2a
  exact Or.inr (And.intro h h2b)

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x h
  have hAuC : x ∈ A ∪ C := Or.inl h
  apply h1 at hAuC
  cases' hAuC with hb hc
  exact hb
  have hAiC := And.intro h hc
  apply h2 at hAiC
  exact hAiC.left

-- Family Intersection World

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x h
  rw [mem_sInter] at h
  have hA : A ∈ F → x ∈ A := h A
  apply hA h1

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h
  rw [mem_sInter] at h
  rw [mem_sInter]
  intro t ht
  apply h1 at ht
  apply (h t) ht

example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  apply Subset.antisymm
  intro x h
  rw [mem_sInter]
  rw [mem_inter_iff] at h
  intro t ht
  rw [mem_pair] at ht
  cases' ht with ht1 ht2
  rw [ht1]
  exact h.left
  rw [ht2]
  exact h.right
  intro x h
  rw [mem_sInter] at h
  rw [mem_inter_iff]
  constructor
  have ha: A ∈ {A, B} := by
    rw [mem_pair A A B]
    left
    rfl
  exact (h A) ha
  have hb: B ∈ {A, B} := by
    rw [mem_pair B A B]
    right
    rfl
  exact (h B) hb

example (F G : Set (Set U)) : ⋂₀ (F ∪ G) = (⋂₀ F) ∩ (⋂₀ G) := by
  apply Subset.antisymm
  intro t h
  rw [mem_inter_iff]
  rw [mem_sInter] at h
  rw [mem_sInter, mem_sInter]
  constructor
  intro x hx
  have hFG : x ∈ F ∨ x ∈ G := by
    exact Or.inl hx
  rw [← mem_union] at hFG
  exact (h x) hFG
  intro x hx
  have hFG : x ∈ F ∨ x ∈ G := by
    exact Or.inr hx
  rw [← mem_union] at hFG
  exact (h x) hFG
  intro t h
  rw [mem_sInter]
  rw [mem_inter_iff] at h
  cases' h with hF hG
  rw [mem_sInter] at hF
  rw [mem_sInter] at hG
  intro x hx
  rw [mem_union] at hx
  cases' hx with hxF hxG
  exact (hF x) hxF
  exact (hG x) hxG

example (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  constructor
  intro h X hX t ht
  apply h at ht
  rw [mem_sInter] at ht
  exact (ht X) hX
  intro h t ht X hX
  have hAX := (h X) hX
  exact hAX ht

example (A : Set U) (F G : Set (Set U)) (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro t htG
  rw [mem_sInter] at htG
  rw [mem_union]
  rw [mem_sInter]
  by_cases h: t ∈ A
  exact Or.inl h
  right
  intro S hS
  apply (h1 S) at hS
  apply (htG (A∪S)) at hS
  rw [mem_union] at hS
  cases' hS with hS1 hS2
  apply h at hS1
  cases' hS1
  exact hS2

-- Family Union World

example (A : Set U) : ∃ s, s ⊆ A := by
  have h: A⊆A := Subset.refl A
  exact Exists.intro A h

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x hx
  rw [mem_sUnion]
  exact Exists.intro A (And.intro h1 hx)

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro t ht
  rw [mem_sUnion]
  rw [mem_sUnion] at ht
  obtain ⟨W, hW⟩ := ht
  cases' hW with hWF htW
  use W
  constructor
  apply h1 at hWF
  exact hWF
  exact htW

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  apply Subset.antisymm
  intro x hx
  rw [mem_sUnion]
  cases' hx with ha hb
  use A
  constructor
  rw [mem_pair]
  left
  rfl
  exact ha
  use B
  constructor
  rw [mem_pair]
  right
  rfl
  exact hb
  intro x hx
  rw [mem_sUnion] at hx
  rw [mem_union]
  obtain ⟨w, hw⟩ := hx
  cases' hw with hw1 hw2
  rw [mem_pair] at hw1
  cases' hw1 with hw1a hw1b
  rw [hw1a] at hw2
  exact Or.inl hw2
  rw [hw1b] at hw2
  exact Or.inr hw2

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  apply Subset.antisymm
  intro x hx
  rw [mem_sUnion] at hx
  rw [mem_union, mem_sUnion, mem_sUnion]
  obtain ⟨W, hW⟩ := hx
  cases' hW
  cases' left
  left
  use W
  right
  use W
  intro x hx
  cases' hx
  rw [mem_sUnion] at h
  rw [mem_sUnion]
  obtain ⟨W, hW⟩ := h
  cases' hW
  use W
  constructor
  apply Or.inl left
  exact right
  rw [mem_sUnion] at h
  rw [mem_sUnion]
  obtain ⟨W, hW⟩ := h
  cases' hW
  use W
  constructor
  apply Or.inr left
  exact right

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  constructor
  intro h X hX t ht
  apply h
  rw [mem_sUnion]
  exact Exists.intro X (And.intro hX ht)
  intro h x hx
  rw [mem_sUnion] at hx
  obtain ⟨W, hW⟩ := hx
  cases' hW
  exact ((h W) left) right

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  apply Subset.antisymm
  intro x hx
  rw [mem_sUnion]
  cases' hx
  rw [mem_sUnion] at right
  obtain ⟨W, hW⟩ := right
  cases' hW
  use (A ∩ W)
  constructor
  rw [mem_setOf]
  use W
  constructor
  exact left
  exact right
  intro x hx
  rw [mem_sUnion] at hx
  rw [mem_inter_iff, mem_sUnion]
  constructor
  obtain ⟨W, hW⟩ := hx
  cases' hW
  rw [mem_setOf] at left
  obtain ⟨L, hL⟩ := left
  cases' hL
  rw [right_1] at right
  cases' right
  exact left_1
  obtain ⟨W, hW⟩ := hx
  cases' hW
  rw [mem_setOf] at left
  obtain ⟨L, hL⟩ := left
  cases' hL
  rw [right_1] at right
  cases' right
  use L

-- Family Combination World

example (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {s | sᶜ ∈ F} := by
  apply Subset.antisymm
  intro x h T hT
  rw [mem_compl_iff, mem_sUnion] at h
  rw [mem_setOf] at hT
  by_contra h1
  apply h
  use Tᶜ
  constructor
  exact hT
  rw [mem_compl_iff]
  exact h1
  intro x h l
  rw [mem_sInter] at h
  rw [mem_sUnion] at l
  obtain ⟨W, hW⟩ := l
  cases' hW
  have hy := h Wᶜ
  rw [mem_setOf, compl_compl] at hy
  apply hy at left
  apply left right

example (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {s | sᶜ ∈ F} := by
  apply Subset.antisymm
  intro x h
  rw [mem_compl_iff] at h
  rw [mem_sInter] at h
  rw [mem_sUnion]
  push_neg at h
  obtain ⟨W, hW⟩ := h
  use Wᶜ
  cases' hW
  constructor
  rw [mem_setOf, compl_compl]
  exact left
  apply right
  intro x h
  rw [mem_compl_iff, mem_sInter]
  rw [mem_sUnion] at h
  obtain ⟨W, hW⟩ := h
  cases' hW
  by_contra hp
  rw [mem_setOf] at left
  have ha := (hp Wᶜ) left
  exact ha right

example (F G : Set (Set U)) (h1 : ∀ s ∈ F, ∃ t ∈ G, s ⊆ t) (h2 : ∃ s ∈ F, ∀ t ∈ G, t ⊆ s) : ∃ u, u ∈ F ∩ G := by
  obtain ⟨WF, hWF⟩ := h2
  cases' hWF
  have h1W := (h1 WF) left
  obtain ⟨WG, hWG⟩ := h1W
  cases' hWG
  have hWGWF := (right WG) left_1
  have WFeqWG := Subset.antisymm right_1 hWGWF
  rw [← WFeqWG] at left_1
  use WF
  constructor
  exact left
  exact left_1

example (F G H : Set (Set U)) (h1 : ∀ s ∈ F, ∃ u ∈ G, s ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
  intro x h
  cases' h
  rw [mem_sUnion] at left
  rw [mem_sInter] at right
  obtain ⟨W, hW⟩ := left
  cases' hW
  rw [mem_sUnion]
  have hWF := (h1 W) left
  obtain ⟨W2, hW2⟩ := hWF
  cases' hW2
  use (W∩W2)
  constructor
  exact right_2
  have hp := (right W2) left_1
  exact And.intro right_1 hp

example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x h
  cases' h with hf hg
  rw [mem_sUnion] at hf
  rw [mem_compl_iff, mem_sUnion] at hg
  rw [mem_sUnion]
  push_neg at hg
  obtain ⟨W, hW⟩ := hf
  cases' hW with ha hb
  have hp := (hg W)
  use W
  constructor
  constructor
  exact ha
  by_contra hl
  rw [mem_compl_iff] at hl
  push_neg at hl
  apply hp at hl
  apply hl at hb
  exact hb
  exact hb

example (F G : Set (Set U)) (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) : (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) := by
  intro x h
  cases' h with hf hg
  rw [mem_sUnion] at hf
  rw [mem_sUnion] at hg
  rw [mem_sUnion]
  obtain ⟨WF, hWF⟩ := hf
  obtain ⟨WG, hWG⟩ := hg
  cases' hWF with hfa hfb
  cases' hWG with hga hgb
  by_cases h : x ∈ ⋃₀ (F ∩ Gᶜ)
  have h2 := h1 h
  rw [mem_sUnion] at h
  cases' h2 with h2l h2r
  rw [mem_sUnion] at h2l
  rw [mem_compl_iff, mem_sUnion] at h2r
  push_neg at h2r
  have f := (h2r WG) hga
  cases' f hgb
  by_cases hp : x ∈ ⋃₀ F ∩ (⋃₀ G)ᶜ
  rw [mem_sUnion] at h
  cases' hp with hp1 hp2
  rw [mem_sUnion] at hp1
  rw [mem_compl_iff, mem_sUnion] at hp2
  push_neg at h
  push_neg at hp2
  have f := (hp2 WG) hga
  cases' f hgb
  rw [mem_sUnion] at h
  push_neg at h
  rw [← mem_compl_iff, compl_inter, compl_compl] at hp
  cases' hp with hp1 hp2
  rw [mem_compl_iff, mem_sUnion] at hp1
  push_neg at hp1
  have f := (hp1 WF) hfa
  cases' f hfb
  rw [mem_sUnion] at hp2
  obtain ⟨W, hW⟩ := hp2
  by_contra ht
  push_neg at ht
  by_cases hp: WF ∈ G
  have hfg := And.intro hfa hp
  have f := (ht WF) hfg
  cases' f hfb
  rw [← mem_compl_iff] at hp
  have hfg := And.intro hfa hp
  have f := (h WF) hfg
  cases' f hfb

example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ vᶜ} := by
  intro x h
  cases' h with hl hr
  rw [mem_sUnion] at hl
  rw [mem_sUnion]
  by_contra h
  rw [mem_compl_iff, mem_sInter] at hr
  push_neg at hr
  push_neg at h
  obtain ⟨WF, hWF⟩ := hl
  obtain ⟨WG, hWG⟩ := hr
  cases' hWF with hf1 hf2
  cases' hWG with hg1 hg2
  have hfg := h (WF ∩ WGᶜ)
  rw [mem_setOf] at hfg
  have hp: ∃ u ∈ F, ∃ v ∈ G, WF ∩ WGᶜ = u ∩ vᶜ := Exists.intro (WF) (And.  intro hf1 (Exists.intro (WG) (And.intro hg1 rfl)))
  apply hfg at hp
  rw [← mem_compl_iff] at hg2
  exact hp (And.intro hf2 hg2)

example (A : Set U) (h1 : ∀ F, (⋃₀ F = A → A ∈ F)) : ∃ x, A = {x} := by
  have h2 := h1 {s | (∃ x, s = {x}) ∧ s ⊆ A}
  rw [mem_setOf] at h2
  have h2p : ⋃₀ {s | (∃ x, s = {x}) ∧ s ⊆ A} = A → ∃ x, A = {x} := by exact fun p => (h2 p).left
  apply h2p
  apply Subset.antisymm
  intro x h
  rw [mem_sUnion] at h
  obtain ⟨W, hW⟩ := h
  cases' hW with hw1 hw2
  rw [mem_setOf] at hw1
  cases' hw1 with hw1a hw1b
  exact hw1b hw2
  intro x h
  rw [mem_sUnion]
  use {x}
  constructor
  rw [mem_setOf]
  constructor
  use x
  intro t ht
  rw [mem_singleton_iff] at ht
  rw [← ht] at h
  exact h
  rw [mem_singleton_iff]
