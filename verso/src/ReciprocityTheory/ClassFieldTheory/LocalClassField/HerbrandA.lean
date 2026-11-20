import Mathlib

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

variable {M : Type*} [AddCommGroup M]

abbrev T (D N : M →+ M) : Type _ := D.ker ⧸ (N.range.addSubgroupOf D.ker)

def IsFin (D N : M →+ M) : Prop := Finite (T D N) ∧ Finite (T N D)

noncomputable def q (D N : M →+ M) : ℚ := (Nat.card (T D N) : ℚ) / (Nat.card (T N D) : ℚ)

structure SES {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (DA NA : A →+ A) (DB NB : B →+ B) (DC NC : C →+ C) (f : A →+ B) (g : B →+ C) : Prop where
  inj : Injective f
  exact : Function.Exact f g
  surj : Surjective g
  fD : ∀ a, f (DA a) = DB (f a)
  fN : ∀ a, f (NA a) = NB (f a)
  gD : ∀ b, g (DB b) = DC (g b)
  gN : ∀ b, g (NB b) = NC (g b)
  DN : ∀ b, DB (NB b) = 0
  ND : ∀ b, NB (DB b) = 0

/- English proof (translation)
Rewrite using `[QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]`.
-/
theorem mk_eq_zero_iff {D N : M →+ M} (x : D.ker) :
    (QuotientAddGroup.mk x : T D N) = 0 ↔ (x : M) ∈ N.range := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

/- English proof (translation)
Rewrite using `[← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]`. Both sides reduce to the same expression.
-/
theorem mk_eq_mk_iff {D N : M →+ M} (x y : D.ker) :
    (QuotientAddGroup.mk x : T D N) = QuotientAddGroup.mk y ↔ (x : M) - y ∈ N.range := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]; rfl

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}

def kerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : DA.ker →+ DB.ker :=
  (f.comp DA.ker.subtype).codRestrict DB.ker (fun a => by
    have ha : DA (a : A) = 0 := a.2
    rw [AddMonoidHom.mem_ker]
    change DB (f a) = 0
    rw [← fD, ha, map_zero])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem kerMap_coe (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (a : DA.ker) :
    ((kerMap f fD a : DB.ker) : B) = f a := rfl

def Tmap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a)) :
    T DA NA →+ T DB NB :=
  QuotientAddGroup.map _ _ (kerMap f fD) (by
    intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := ha
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact ⟨f x, by rw [← fN, hx]; rfl⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem Tmap_mk (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (a : DA.ker) : Tmap f fD fN (QuotientAddGroup.mk a) = QuotientAddGroup.mk (kerMap f fD a) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.inj, h.exact, h.surj, h.fN, h.fD, h.gN, h.gD, h.ND, h.DN⟩`.
-/
theorem SES.swap (h : SES DA NA DB NB DC NC f g) : SES NA DA NB DB NC DC f g :=
  ⟨h.inj, h.exact, h.surj, h.fN, h.fD, h.gN, h.gD, h.ND, h.DN⟩

/- English proof (translation)
Take `⟨b, rfl⟩` from `h.surj c`. Rewrite using `[← h.gN, ← h.gD, h.DN, map_zero]`.
-/
theorem SES.DN_C (h : SES DA NA DB NB DC NC f g) (c : C) : DC (NC c) = 0 := by
  obtain ⟨b, rfl⟩ := h.surj c
  rw [← h.gN, ← h.gD, h.DN, map_zero]

/- English proof (translation)
Use extensionality with `x`. Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Rewrite using `[AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`.

Take `⟨b', rfl⟩` from `h.surj c`. Establish `h1 : g ((b : B) - NB b') = 0` using `by rw [map_sub, h.gN, hc, sub_self]`. Take `⟨a, ha⟩` from `(h.exact _).1 h1`. Establish `hb : DB (b : B) = 0` using `b.2`. Establish `haD : DA a = 0` using `h.inj (by rw [h.fD, ha, map_sub, hb, h.DN, sub_zero, map_zero])`.

Use `⟨QuotientAddGroup.mk ⟨a, haD⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Tmap_mk, mk_eq_mk_iff, kerMap_coe]`. Conclude with `⟨-b', by rw [map_neg]; change _ = f a - b; rw [ha]; abel⟩`. Introduce and unpack `⟨y, hy⟩`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective y`.

Rewrite `hy` using `[Tmap_mk, mk_eq_mk_iff, kerMap_coe]`. Take `⟨b', hb'⟩` from `hy`. Use `⟨- g b', ?_⟩` and prove the remaining obligations. Establish `h0 : g (f a) = 0` using `(h.exact _).2 ⟨a, rfl⟩`. Use `congrArg g hb'` as an intermediate fact.

Rewrite `this` using `[map_sub, h0, h.gN, zero_sub]`. Rewrite using `[map_neg, this, neg_neg]`.
-/
theorem ker_Tmap_g (h : SES DA NA DB NB DC NC f g) :
    (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range := by
  ext x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b', rfl⟩ := h.surj c
    have h1 : g ((b : B) - NB b') = 0 := by rw [map_sub, h.gN, hc, sub_self]
    obtain ⟨a, ha⟩ := (h.exact _).1 h1
    have hb : DB (b : B) = 0 := b.2
    have haD : DA a = 0 := h.inj (by rw [h.fD, ha, map_sub, hb, h.DN, sub_zero, map_zero])
    refine ⟨QuotientAddGroup.mk ⟨a, haD⟩, ?_⟩
    rw [Tmap_mk, mk_eq_mk_iff, kerMap_coe]
    exact ⟨-b', by rw [map_neg]; change _ = f a - b; rw [ha]; abel⟩
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [Tmap_mk, mk_eq_mk_iff, kerMap_coe] at hy
    obtain ⟨b', hb'⟩ := hy
    refine ⟨- g b', ?_⟩
    have h0 : g (f a) = 0 := (h.exact _).2 ⟨a, rfl⟩
    have := congrArg g hb'
    rw [map_sub, h0, h.gN, zero_sub] at this
    rw [map_neg, this, neg_neg]

def Rel (DB : B →+ B) (f : A →+ B) (g : B →+ C) (c : C) (a : A) : Prop := ∃ b, g b = c ∧ f a = DB b

/- English proof (translation)
Take `⟨b, hb⟩` from `h.surj c`. Establish `hc : DC (c : C) = 0` using `c.2`. Establish `h1 : g (DB b) = 0` using `by rw [h.gD, hb, hc]`. Take `⟨a, ha⟩` from `(h.exact _).1 h1`. Conclude with `⟨⟨a, h.inj (by rw [h.fN, ha, h.ND, map_zero])⟩, b, hb, ha⟩`.
-/
theorem exists_rel (h : SES DA NA DB NB DC NC f g) (c : DC.ker) : ∃ a : NA.ker, Rel DB f g c a := by
  obtain ⟨b, hb⟩ := h.surj c
  have hc : DC (c : C) = 0 := c.2
  have h1 : g (DB b) = 0 := by rw [h.gD, hb, hc]
  obtain ⟨a, ha⟩ := (h.exact _).1 h1
  exact ⟨⟨a, h.inj (by rw [h.fN, ha, h.ND, map_zero])⟩, b, hb, ha⟩

/- English proof (translation)
Take `⟨b, hb, ha⟩` from `h1`. Take `⟨b', hb', ha'⟩` from `h2`. Rewrite using `[mk_eq_mk_iff]`. Take `⟨x, hx⟩` from `(h.exact (b - b')).1 (by rw [map_sub, hb, hb', sub_self])`. Conclude with `⟨x, h.inj (by rw [h.fD, hx, map_sub, map_sub, ha, ha'])⟩`.
-/
theorem rel_unique (h : SES DA NA DB NB DC NC f g) {c : C} {a a' : NA.ker} (h1 : Rel DB f g c a)
    (h2 : Rel DB f g c a') : (QuotientAddGroup.mk a : T NA DA) = QuotientAddGroup.mk a' := by
  obtain ⟨b, hb, ha⟩ := h1
  obtain ⟨b', hb', ha'⟩ := h2
  rw [mk_eq_mk_iff]
  obtain ⟨x, hx⟩ := (h.exact (b - b')).1 (by rw [map_sub, hb, hb', sub_self])
  exact ⟨x, h.inj (by rw [h.fD, hx, map_sub, map_sub, ha, ha'])⟩

/- English proof (translation)
Set `δ0 : DC.ker →+ T NA DA` to `AddMonoidHom.mk' (fun c => QuotientAddGroup.mk (Classical.choose (exists_rel h c))) (fun c c' => by`. Rewrite using `[← QuotientAddGroup.mk_add]`. Use `rel_unique h (Classical.choose_spec (exists_rel h (c + c'))) ?_` and prove the remaining obligations. Take `⟨b, hb, ha⟩` from `Classical.choose_spec (exists_rel h c)`. Take `⟨b', hb', ha'⟩` from `Classical.choose_spec (exists_rel h c')`.

Conclude with `⟨b + b', by rw [map_add, hb, hb']; rfl, by`. Rewrite using `[map_add, ← ha, ← ha', ← map_add]`. Use the proof step `rfl⟩)`. Establish `hδ0 : ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a → δ0 c = QuotientAddGroup.mk a` using `fun c a hca => rel_unique h (Classical.choose_spec (exists_rel h c)) hca`. Use `⟨QuotientAddGroup.lift _ δ0 ?_, fun c a hca => ?_⟩` and prove the remaining obligations.

Introduce `c hc`. Rewrite `hc` using `[AddSubgroup.mem_addSubgroupOf]`. Take `⟨c0, hc0⟩` from `hc`. Take `⟨b0, rfl⟩` from `h.surj c0`. Rewrite using `[AddMonoidHom.mem_ker, hδ0 c 0 ⟨NB b0, by rw [h.gN, hc0], by rw [h.DN]; exact map_zero f⟩]`.

Both sides reduce to the same expression. Rewrite using `[QuotientAddGroup.lift_mk]`. Conclude with `hδ0 c a hca`.
-/
theorem exists_delta (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a →
      δ (QuotientAddGroup.mk c) = QuotientAddGroup.mk a := by
  classical
  let δ0 : DC.ker →+ T NA DA := AddMonoidHom.mk'
    (fun c => QuotientAddGroup.mk (Classical.choose (exists_rel h c))) (fun c c' => by
      rw [← QuotientAddGroup.mk_add]
      refine rel_unique h (Classical.choose_spec (exists_rel h (c + c'))) ?_
      obtain ⟨b, hb, ha⟩ := Classical.choose_spec (exists_rel h c)
      obtain ⟨b', hb', ha'⟩ := Classical.choose_spec (exists_rel h c')
      exact ⟨b + b', by rw [map_add, hb, hb']; rfl, by
        rw [map_add, ← ha, ← ha', ← map_add]; rfl⟩)
  have hδ0 : ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a → δ0 c = QuotientAddGroup.mk a :=
    fun c a hca => rel_unique h (Classical.choose_spec (exists_rel h c)) hca
  refine ⟨QuotientAddGroup.lift _ δ0 ?_, fun c a hca => ?_⟩
  · intro c hc
    rw [AddSubgroup.mem_addSubgroupOf] at hc
    obtain ⟨c0, hc0⟩ := hc
    obtain ⟨b0, rfl⟩ := h.surj c0
    rw [AddMonoidHom.mem_ker, hδ0 c 0 ⟨NB b0, by rw [h.gN, hc0], by rw [h.DN]; exact map_zero f⟩]
    rfl
  · rw [QuotientAddGroup.lift_mk]
    exact hδ0 c a hca

/- English proof (translation)
Take `⟨δ, hδ⟩` from `exists_delta h`. Use `⟨δ, ker_Tmap_g h, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Take `⟨c, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨a, b, hb, ha⟩` from `exists_rel h c`. Rewrite `hx` using `[AddMonoidHom.mem_ker, hδ c a ⟨b, hb, ha⟩, mk_eq_zero_iff]`. Take `⟨a', ha'⟩` from `hx`. Establish `hk : DB (b - f a') = 0` using `by rw [map_sub, ← h.fD, ha', ha, sub_self]`.

Use `⟨QuotientAddGroup.mk ⟨b - f a', hk⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Tmap_mk]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[kerMap_coe]`.

Express the relevant statement in the definitionally equal form `g (b - f a') = c`. Rewrite using `[map_sub, (h.exact _).2 ⟨a', rfl⟩, sub_zero, hb]`. Introduce and unpack `⟨y, hy⟩`. Take `⟨b, rfl⟩` from `QuotientAddGroup.mk_surjective y`. Rewrite `hy` using `[Tmap_mk]`.

Establish `hb : DB (b : B) = 0` using `b.2`. Rewrite using `[AddMonoidHom.mem_ker, ← hy, hδ _ 0 ⟨b, rfl, by rw [hb]; exact map_zero f⟩]`. Both sides reduce to the same expression. Use extensionality with `y`. Take `⟨a, rfl⟩` from `QuotientAddGroup.mk_surjective y`.

Rewrite using `[AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb⟩`. Establish `hc : DC (g b) = 0` using `by rw [← h.gD, hb]; exact (h.exact _).2 ⟨a, rfl⟩`. Conclude with `⟨QuotientAddGroup.mk ⟨g b, hc⟩, hδ _ a ⟨b, rfl, hb.symm⟩⟩`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨c, rfl⟩` from `QuotientAddGroup.mk_surjective x`. Take `⟨a', b, hb, ha'⟩` from `exists_rel h c`. Rewrite `hx` using `[hδ c a' ⟨b, hb, ha'⟩, mk_eq_mk_iff]`. Take `⟨a'', ha''⟩` from `hx`.

Use `⟨b - f a'', ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← h.fD, ha'', map_sub, ha']`. Normalize the expressions using the abelian group laws.
-/
theorem half_hexagon (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range ∧
      δ.ker = (Tmap g h.gD h.gN).range ∧ (Tmap f h.fN h.fD).ker = δ.range := by
  obtain ⟨δ, hδ⟩ := exists_delta h
  refine ⟨δ, ker_Tmap_g h, ?_, ?_⟩
  · ext x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    constructor
    · intro hx
      obtain ⟨a, b, hb, ha⟩ := exists_rel h c
      rw [AddMonoidHom.mem_ker, hδ c a ⟨b, hb, ha⟩, mk_eq_zero_iff] at hx
      obtain ⟨a', ha'⟩ := hx
      have hk : DB (b - f a') = 0 := by rw [map_sub, ← h.fD, ha', ha, sub_self]
      refine ⟨QuotientAddGroup.mk ⟨b - f a', hk⟩, ?_⟩
      rw [Tmap_mk]
      congr 1
      apply Subtype.ext
      rw [kerMap_coe]
      change g (b - f a') = c
      rw [map_sub, (h.exact _).2 ⟨a', rfl⟩, sub_zero, hb]
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [Tmap_mk] at hy
      have hb : DB (b : B) = 0 := b.2
      rw [AddMonoidHom.mem_ker, ← hy, hδ _ 0 ⟨b, rfl, by rw [hb]; exact map_zero f⟩]
      rfl
  · ext y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]
    constructor
    · rintro ⟨b, hb⟩
      have hc : DC (g b) = 0 := by rw [← h.gD, hb]; exact (h.exact _).2 ⟨a, rfl⟩
      exact ⟨QuotientAddGroup.mk ⟨g b, hc⟩, hδ _ a ⟨b, rfl, hb.symm⟩⟩
    · rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨a', b, hb, ha'⟩ := exists_rel h c
      rw [hδ c a' ⟨b, hb, ha'⟩, mk_eq_mk_iff] at hx
      obtain ⟨a'', ha''⟩ := hx
      refine ⟨b - f a'', ?_⟩
      rw [map_sub, ← h.fD, ha'', map_sub, ha']
      abel

section Count

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

/- English proof (translation)
Rewrite using `[← AddSubgroup.index_ker, AddSubgroup.card_mul_index]`.
-/
theorem card_eq_ker_mul_range (φ : X →+ Y) :
    Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

/- English proof (translation)
Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[card_eq_ker_mul_range ψ, hex]`. Establish `: Finite φ.range` using `Set.finite_range φ`. Conclude with `Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'`.
-/
theorem finite_of_exact (φ : X →+ Y) (ψ : Y →+ Z) (hex : ψ.ker = φ.range) [Finite X] [Finite Z] :
    Finite Y := by
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_ker_mul_range ψ, hex]
  have : Finite φ.range := Set.finite_range φ
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

/- English proof (translation)
Rewrite using `[card_eq_ker_mul_range f₁, card_eq_ker_mul_range f₂, card_eq_ker_mul_range f₃, card_eq_ker_mul_range f₄, card_eq_ker_mul_range f₅, card_eq_ker_mul_range f₆, h₁, h₂, h₃, h₄, h₅, h₆]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem card_six {X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [AddCommGroup X₄] [AddCommGroup X₅] [AddCommGroup X₆] (f₁ : X₁ →+ X₂) (f₂ : X₂ →+ X₃)
    (f₃ : X₃ →+ X₄) (f₄ : X₄ →+ X₅) (f₅ : X₅ →+ X₆) (f₆ : X₆ →+ X₁) (h₁ : f₂.ker = f₁.range)
    (h₂ : f₃.ker = f₂.range) (h₃ : f₄.ker = f₃.range) (h₄ : f₅.ker = f₄.range)
    (h₅ : f₆.ker = f₅.range) (h₆ : f₁.ker = f₆.range) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ = Nat.card X₂ * Nat.card X₄ * Nat.card X₆ := by
  rw [card_eq_ker_mul_range f₁, card_eq_ker_mul_range f₂, card_eq_ker_mul_range f₃,
    card_eq_ker_mul_range f₄, card_eq_ker_mul_range f₅, card_eq_ker_mul_range f₆, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

end Count

/- English proof (translation)
Take `⟨δ, h1, h2, h3⟩` from `half_hexagon h`. Take `⟨δ', h4, h5, h6⟩` from `half_hexagon h.swap`. Conclude with `card_six _ _ _ _ _ _ h1 h2 h3 h4 h5 h6`.
-/
theorem card_hexagon (h : SES DA NA DB NB DC NC f g) :
    Nat.card (T DA NA) * Nat.card (T DC NC) * Nat.card (T NB DB) =
      Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC) := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  exact card_six _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

/- English proof (translation)
Take `⟨δ, h1, h2, h3⟩` from `half_hexagon h`. Take `⟨δ', h4, h5, h6⟩` from `half_hexagon h.swap`. Take `⟨_, _⟩` from `hA`. Take `⟨_, _⟩` from `hC`. Conclude with `⟨finite_of_exact _ _ h1, finite_of_exact _ _ h4⟩`.
-/
theorem isFin_mid (h : SES DA NA DB NB DC NC f g) (hA : IsFin DA NA) (hC : IsFin DC NC) :
    IsFin DB NB := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  exact ⟨finite_of_exact _ _ h1, finite_of_exact _ _ h4⟩

/- English proof (translation)
Take `⟨δ, h1, h2, h3⟩` from `half_hexagon h`. Take `⟨δ', h4, h5, h6⟩` from `half_hexagon h.swap`. Take `⟨_, _⟩` from `hB`. Take `⟨_, _⟩` from `hC`. Conclude with `⟨finite_of_exact _ _ h6, finite_of_exact _ _ h3⟩`.
-/
theorem isFin_left (h : SES DA NA DB NB DC NC f g) (hB : IsFin DB NB) (hC : IsFin DC NC) :
    IsFin DA NA := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  obtain ⟨_, _⟩ := hB
  obtain ⟨_, _⟩ := hC
  exact ⟨finite_of_exact _ _ h6, finite_of_exact _ _ h3⟩

/- English proof (translation)
Establish `hB` using `isFin_mid h hA hC`. Establish `key` using `card_hexagon h`. Take `⟨_, _⟩` from `hA`. Take `⟨_, _⟩` from `hB`. Take `⟨_, _⟩` from `hC`.

Establish `e1 : (Nat.card (T NA DA) : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `e2 : (Nat.card (T NB DB) : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `e3 : (Nat.card (T NC DC) : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `key' : (Nat.card (T DA NA) : ℚ) * Nat.card (T DC NC) * Nat.card (T NB DB) = Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC)` using `by exact_mod_cast key`. Unfold `q`.

Clear the denominators using the available nonvanishing facts. Combine the linear relations using `[key']`.
-/
theorem q_mul (h : SES DA NA DB NB DC NC f g) (hA : IsFin DA NA) (hC : IsFin DC NC) :
    q DB NB = q DA NA * q DC NC := by
  have hB := isFin_mid h hA hC
  have key := card_hexagon h
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  obtain ⟨_, _⟩ := hC
  have e1 : (Nat.card (T NA DA) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e2 : (Nat.card (T NB DB) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e3 : (Nat.card (T NC DC) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key' : (Nat.card (T DA NA) : ℚ) * Nat.card (T DC NC) * Nat.card (T NB DB) =
      Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC) := by exact_mod_cast key
  unfold q
  field_simp
  linarith [key']

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance⟩`.
-/
theorem isFin_of_finite [Finite M] (D N : M →+ M) : IsFin D N := ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Establish `h1 : Nat.card D.ker = Nat.card (T D N) * Nat.card N.range`. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (N.range.addSubgroupOf D.ker)]`. Use `congr 1`. Conclude with `Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by`. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `hDN x)).toEquiv`. Establish `h2 : Nat.card N.ker = Nat.card (T N D) * Nat.card D.range`. Rewrite using `[AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (D.range.addSubgroupOf N.ker)]`. Use `congr 1`. Conclude with `Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `hND x)).toEquiv`. Establish `h3` using `card_eq_ker_mul_range D`. Establish `h4` using `card_eq_ker_mul_range N`. Rewrite `h3` using `[h1]`.

Rewrite `h4` using `[h2]`. Establish `h5 : Nat.card (T D N) * (Nat.card N.range * Nat.card D.range) = Nat.card (T N D) * (Nat.card N.range * Nat.card D.range)`. Combine the equalities or inequalities in the displayed calculation. Establish `h6 : Nat.card (T D N) = Nat.card (T N D)` using `Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) h5`. Unfold `q`.

Rewrite using `[h6]`. Conclude with `div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')`.
-/
theorem q_of_finite [Finite M] (D N : M →+ M) (hDN : ∀ x, D (N x) = 0) (hND : ∀ x, N (D x) = 0) :
    q D N = 1 := by
  have h1 : Nat.card D.ker = Nat.card (T D N) * Nat.card N.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (N.range.addSubgroupOf D.ker)]
    congr 1
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by
      rintro _ ⟨x, rfl⟩; exact hDN x)).toEquiv
  have h2 : Nat.card N.ker = Nat.card (T N D) * Nat.card D.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (D.range.addSubgroupOf N.ker)]
    congr 1
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by
      rintro _ ⟨x, rfl⟩; exact hND x)).toEquiv
  have h3 := card_eq_ker_mul_range D
  have h4 := card_eq_ker_mul_range N
  rw [h1] at h3
  rw [h2] at h4
  have h5 : Nat.card (T D N) * (Nat.card N.range * Nat.card D.range) =
      Nat.card (T N D) * (Nat.card N.range * Nat.card D.range) := by
    calc _ = Nat.card M := by rw [h3]; ring
      _ = _ := by rw [h4]; ring
  have h6 : Nat.card (T D N) = Nat.card (T N D) :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) h5
  unfold q
  rw [h6]
  exact div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
