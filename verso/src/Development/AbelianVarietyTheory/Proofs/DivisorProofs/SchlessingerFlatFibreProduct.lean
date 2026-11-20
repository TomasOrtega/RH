import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RTensorInjectiveOfPowSmulEqBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTensorInjectiveOfFlatBaseChangeKerInfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatQuotientSmulTopOfSurjectiveFlatStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace GlobalTheory.SchlessingerFlat

/- English proof (translation)
Introduce `P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h x y hxy`. Establish `H` using `(Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))`. Take `⟨p, hp₁, hp₂⟩` from `H.2.2 x y hxy`. Conclude with `⟨p, ⟨hp₁, hp₂⟩, fun q hq => H.2.1 q p ⟨hq.1.trans hp₁.symm, hq.2.trans hp₂.symm⟩⟩`.
-/
theorem exists_unique_of_isPullback : ∀ {P R₁ R₂ R₀ : CommRingCat.{0}} (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → ∀ (x : R₁) (y : R₂), g₁.hom x = g₂.hom y → ∃! p : P, f₁.hom p = x ∧ f₂.hom p = y := by
  intro P R₁ R₂ R₀ f₁ f₂ g₁ g₂ h x y hxy
  have H := (Types.isPullback_iff _ _ _ _).1 (h.map (forget CommRingCat))
  obtain ⟨p, hp₁, hp₂⟩ := H.2.2 x y hxy
  exact ⟨p, ⟨hp₁, hp₂⟩, fun q hq => H.2.1 q p ⟨hq.1.trans hp₁.symm, hq.2.trans hp₂.symm⟩⟩

/- English proof (translation)
Introduce `P R B C a f c a' w hf hc hk`. Establish `hw : ∀ p, c.hom (a.hom p) = a'.hom (f.hom p)` using `fun p => congr($(w) p)`. Establish `key : ∀ (s : PushoutCocone a f), RingHom.ker c.hom ≤ RingHom.ker s.inl.hom`. Introduce `s`. Rewrite using `[hk, Ideal.map_le_iff_le_comap]`.

Introduce `p hp`. Establish `e : s.inl.hom (a.hom p) = s.inr.hom (f.hom p)` using `congr($(s.condition) p)`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, e, (RingHom.mem_ker).mp hp, map_zero]`. Set `d : ∀ (s : PushoutCocone a f), C ⟶ s.pt` to `fun s => CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker c.hom) s.inl.hom (fun x hx => key s hx)).comp (RingHom.quotientKerEquivOfSurjective hc).symm.toRingHom)`. Establish `hd : ∀ (s : PushoutCocone a f) (b : B), (d s).hom (c.hom b) = s.inl.hom b`.

Introduce `s b`. Establish `: (RingHom.quotientKerEquivOfSurjective hc).symm (c.hom b) = Ideal.Quotient.mk _ b`. Apply `(RingHom.quotientKerEquivOfSurjective hc).injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Simplify using `[d, this]`.

Both sides reduce to the same expression. Use `⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s`. Use extensionality with `b`. Conclude with `hd s b`.

Introduce `s`. Use extensionality with `r`. Take `⟨p, rfl⟩` from `hf r`. Express the relevant statement in the definitionally equal form `(d s).hom (a'.hom (f.hom p)) = s.inr.hom (f.hom p)`. Rewrite using `[← hw, hd]`.

Conclude with `congr($(s.condition) p)`. Introduce `s m h1 _`. Use extensionality with `x`. Take `⟨b, rfl⟩` from `hc x`. Rewrite using `[hd]`.

Conclude with `congr($(h1) b)`.
-/
theorem isPushout_of_surjective_of_ker : ∀ {P R B C : CommRingCat.{0}} (a : P ⟶ B) (f : P ⟶ R) (c : B ⟶ C) (a' : R ⟶ C), a ≫ c = f ≫ a' → Function.Surjective f → Function.Surjective c → RingHom.ker c.hom = (RingHom.ker f.hom).map a.hom → IsPushout a f c a' := by
  intro P R B C a f c a' w hf hc hk
  have hw : ∀ p, c.hom (a.hom p) = a'.hom (f.hom p) := fun p => congr($(w) p)
  have key : ∀ (s : PushoutCocone a f), RingHom.ker c.hom ≤ RingHom.ker s.inl.hom := by
    intro s
    rw [hk, Ideal.map_le_iff_le_comap]
    intro p hp
    have e : s.inl.hom (a.hom p) = s.inr.hom (f.hom p) := congr($(s.condition) p)
    rw [Ideal.mem_comap, RingHom.mem_ker, e, (RingHom.mem_ker).mp hp, map_zero]
  let d : ∀ (s : PushoutCocone a f), C ⟶ s.pt := fun s =>
    CommRingCat.ofHom ((Ideal.Quotient.lift (RingHom.ker c.hom) s.inl.hom (fun x hx => key s hx)).comp
      (RingHom.quotientKerEquivOfSurjective hc).symm.toRingHom)
  have hd : ∀ (s : PushoutCocone a f) (b : B), (d s).hom (c.hom b) = s.inl.hom b := by
    intro s b
    have : (RingHom.quotientKerEquivOfSurjective hc).symm (c.hom b) = Ideal.Quotient.mk _ b := by
      apply (RingHom.quotientKerEquivOfSurjective hc).injective
      simp
    simp [d, this]
    rfl
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _ d ?_ ?_ ?_⟩⟩
  · intro s; ext b; exact hd s b
  · intro s; ext r
    obtain ⟨p, rfl⟩ := hf r
    change (d s).hom (a'.hom (f.hom p)) = s.inr.hom (f.hom p)
    rw [← hw, hd]
    exact congr($(s.condition) p)
  · intro s m h1 _
    ext x
    obtain ⟨b, rfl⟩ := hc x
    rw [hd]
    exact congr($(h1) b)

/- English proof (translation)
Introduce `R₁ R₀ B₁ B₀ a₁ g₁ b₁ a₀ h hg`. Set `J : Ideal B₁` to `(RingHom.ker g₁.hom).map a₁.hom`. Set `q : B₁ ⟶ CommRingCat.of (B₁ ⧸ J)` to `CommRingCat.ofHom (Ideal.Quotient.mk J)`. Set `a' : R₀ ⟶ CommRingCat.of (B₁ ⧸ J)` to `CommRingCat.ofHom ((Ideal.quotientMap J a₁.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom)`. Establish `w : a₁ ≫ q = g₁ ≫ a'`.

Use extensionality with `r`. Establish `e0 : (RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r) = Ideal.Quotient.mk _ r`. Apply `(RingHom.quotientKerEquivOfSurjective hg).injective` to reduce the goal to its premises. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J (a₁.hom r) = Ideal.quotientMap J a₁.hom Ideal.le_comap_map ((RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r))`.

Rewrite using `[e0]`. Both sides reduce to the same expression. Establish `h'` using `isPushout_of_surjective_of_ker a₁ g₁ q a' w hg Ideal.Quotient.mk_surjective Ideal.mk_ker`. Establish `e` using `IsPushout.inl_isoIsPushout_hom _ _ h h'`. Set `φ` to `h.isoIsPushout _ _ h'`.

Establish `hb : ∀ x, φ.hom.hom (b₁.hom x) = Ideal.Quotient.mk J x` using `fun x => congr($(e) x)`. Establish `hinj : Function.Injective φ.hom.hom` using `fun x y hxy => by`. Simplify using `using congrArg φ.inv.hom hxy`. Use `⟨fun y => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `Ideal.Quotient.mk_surjective (φ.hom.hom y)`.

Conclude with `⟨x, hinj (by rw [hb, hx])⟩`. Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hb]`. Prove the components needed by the constructor for the conclusion. Introduce `h0`.

Rewrite using `[h0, map_zero]`. Introduce `h0`. Conclude with `hinj (h0.trans (map_zero _).symm)`.
-/
theorem surjective_ker_of_isPushout : ∀ {R₁ R₀ B₁ B₀ : CommRingCat.{0}} (a₁ : R₁ ⟶ B₁) (g₁ : R₁ ⟶ R₀) (b₁ : B₁ ⟶ B₀) (a₀ : R₀ ⟶ B₀), IsPushout a₁ g₁ b₁ a₀ → Function.Surjective g₁ → Function.Surjective b₁ ∧ RingHom.ker b₁.hom = (RingHom.ker g₁.hom).map a₁.hom := by
  intro R₁ R₀ B₁ B₀ a₁ g₁ b₁ a₀ h hg
  let J : Ideal B₁ := (RingHom.ker g₁.hom).map a₁.hom
  let q : B₁ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let a' : R₀ ⟶ CommRingCat.of (B₁ ⧸ J) := CommRingCat.ofHom
    ((Ideal.quotientMap J a₁.hom Ideal.le_comap_map).comp (RingHom.quotientKerEquivOfSurjective hg).symm.toRingHom)
  have w : a₁ ≫ q = g₁ ≫ a' := by
    ext r
    have e0 : (RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r) = Ideal.Quotient.mk _ r := by
      apply (RingHom.quotientKerEquivOfSurjective hg).injective
      simp
    change Ideal.Quotient.mk J (a₁.hom r) = Ideal.quotientMap J a₁.hom Ideal.le_comap_map ((RingHom.quotientKerEquivOfSurjective hg).symm (g₁.hom r))
    rw [e0]
    rfl
  have h' := isPushout_of_surjective_of_ker a₁ g₁ q a' w hg Ideal.Quotient.mk_surjective Ideal.mk_ker
  have e := IsPushout.inl_isoIsPushout_hom _ _ h h'
  let φ := h.isoIsPushout _ _ h'
  have hb : ∀ x, φ.hom.hom (b₁.hom x) = Ideal.Quotient.mk J x := fun x => congr($(e) x)
  have hinj : Function.Injective φ.hom.hom := fun x y hxy => by
    simpa using congrArg φ.inv.hom hxy
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (φ.hom.hom y)
    exact ⟨x, hinj (by rw [hb, hx])⟩
  · ext x
    rw [RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← hb]
    constructor
    · intro h0; rw [h0, map_zero]
    · intro h0; exact hinj (h0.trans (map_zero _).symm)

/- English proof (translation)
Introduce `P R₁ R₂ B B₁ B₂ _ _ _ _ _ _ f₁ f₂ a a₁ a₂ c₁ c₂ I₂ w₁ w₂ hc₂ hlift hj hker`. Establish `w₁' : ∀ p, c₁ (a p) = a₁ (f₁ p)` using `fun p => by simpa using RingHom.congr_fun w₁ p`. Establish `w₂' : ∀ p, c₂ (a p) = a₂ (f₂ p)` using `fun p => by simpa using RingHom.congr_fun w₂ p`. Establish `claim : ∀ y ∈ I₂.map a₂, ∃ z ∈ (RingHom.ker f₁).map a, c₁ z = 0 ∧ c₂ z = y`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk, rfl⟩` from `hx`. Take `⟨p, hp1, hp2⟩` from `hlift k hk`. Conclude with `⟨a p, Ideal.mem_map_of_mem _ hp1, by rw [w₁', hp1, map_zero], by rw [w₂', hp2]⟩`.

Consider the case `zero => exact ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩`. Consider the case `add u v _ _ hu hv`. Take `⟨z1, h1, e1, e1'⟩` from `hu`. Take `⟨z2, h2, e2, e2'⟩` from `hv`. Conclude with `⟨z1 + z2, Ideal.add_mem _ h1 h2, by rw [map_add, e1, e2, add_zero], by rw [map_add, e1', e2']⟩`.

Consider the case `smul s u _ hu`. Take `⟨z, hz, e, e'⟩` from `hu`. Take `⟨t, rfl⟩` from `hc₂ s`. Conclude with `⟨t * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, e, mul_zero], by rw [map_mul, e', smul_eq_mul]⟩`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Take `⟨z, hz, e, e'⟩` from `claim _ (hker x hx)`. Establish `h0 : x - z = 0` using `hj _ (by rw [map_sub, hx, e, sub_zero]) (by rw [map_sub, e', sub_self])`. Rewrite using `[sub_eq_zero.mp h0]`.

Conclude with `hz`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `p hp`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, w₁', (RingHom.mem_ker).mp hp, map_zero]`.
-/
theorem ker_eq_map_of_fibre : ∀ (P R₁ R₂ B B₁ B₂ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing B] [CommRing B₁] [CommRing B₂] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (a : P →+* B) (a₁ : R₁ →+* B₁) (a₂ : R₂ →+* B₂) (c₁ : B →+* B₁) (c₂ : B →+* B₂) (I₂ : Ideal R₂), c₁.comp a = a₁.comp f₁ → c₂.comp a = a₂.comp f₂ → Function.Surjective c₂ → (∀ k ∈ I₂, ∃ p : P, f₁ p = 0 ∧ f₂ p = k) → (∀ x : B, c₁ x = 0 → c₂ x = 0 → x = 0) → (∀ x : B, c₁ x = 0 → c₂ x ∈ I₂.map a₂) → RingHom.ker c₁ = (RingHom.ker f₁).map a := by
  intro P R₁ R₂ B B₁ B₂ _ _ _ _ _ _ f₁ f₂ a a₁ a₂ c₁ c₂ I₂ w₁ w₂ hc₂ hlift hj hker
  have w₁' : ∀ p, c₁ (a p) = a₁ (f₁ p) := fun p => by simpa using RingHom.congr_fun w₁ p
  have w₂' : ∀ p, c₂ (a p) = a₂ (f₂ p) := fun p => by simpa using RingHom.congr_fun w₂ p
  have claim : ∀ y ∈ I₂.map a₂, ∃ z ∈ (RingHom.ker f₁).map a, c₁ z = 0 ∧ c₂ z = y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      obtain ⟨p, hp1, hp2⟩ := hlift k hk
      exact ⟨a p, Ideal.mem_map_of_mem _ hp1, by rw [w₁', hp1, map_zero], by rw [w₂', hp2]⟩
    | zero => exact ⟨0, Ideal.zero_mem _, map_zero _, map_zero _⟩
    | add u v _ _ hu hv =>
      obtain ⟨z1, h1, e1, e1'⟩ := hu
      obtain ⟨z2, h2, e2, e2'⟩ := hv
      exact ⟨z1 + z2, Ideal.add_mem _ h1 h2, by rw [map_add, e1, e2, add_zero], by rw [map_add, e1', e2']⟩
    | smul s u _ hu =>
      obtain ⟨z, hz, e, e'⟩ := hu
      obtain ⟨t, rfl⟩ := hc₂ s
      exact ⟨t * z, Ideal.mul_mem_left _ _ hz, by rw [map_mul, e, mul_zero], by rw [map_mul, e', smul_eq_mul]⟩
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨z, hz, e, e'⟩ := claim _ (hker x hx)
    have h0 : x - z = 0 := hj _ (by rw [map_sub, hx, e, sub_zero]) (by rw [map_sub, e', sub_self])
    rw [sub_eq_zero.mp h0]
    exact hz
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker, w₁', (RingHom.mem_ker).mp hp, map_zero]

/- English proof (translation)
Introduce `P R₁ R₂ R₀ _ _ _ _ f₁ f₂ g₁ g₂ w hj hn`. Take `⟨n, hn⟩` from `hn`. Use `⟨n + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.zero_eq_bot, eq_bot_iff]`. Introduce `x hx`.

Establish `h1 : x ∈ RingHom.ker f₁` using `Ideal.pow_le_self (Nat.succ_ne_zero n) hx`. Establish `hle : (RingHom.ker f₁).map f₂ ≤ RingHom.ker g₂`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `y hy`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, ← w, RingHom.comp_apply, (RingHom.mem_ker).mp hy, map_zero]`.

Establish `h2 : f₂ x ∈ (RingHom.ker g₂) ^ (n + 1)`. Use `Ideal.mem_map_of_mem f₂ hx` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hle _ this`. Rewrite `h2` using `[pow_succ, hn, Submodule.zero_eq_bot, Submodule.bot_mul]`.

Establish `h3 : x ∈ RingHom.ker f₁ ⊓ RingHom.ker f₂` using `⟨h1, by simpa using h2⟩`. Rewrite `h3` using `[hj]`. Conclude with `h3`.
-/
theorem isNilpotent_ker_of_fibre : ∀ (P R₁ R₂ R₀ : Type) [CommRing P] [CommRing R₁] [CommRing R₂] [CommRing R₀] (f₁ : P →+* R₁) (f₂ : P →+* R₂) (g₁ : R₁ →+* R₀) (g₂ : R₂ →+* R₀), g₁.comp f₁ = g₂.comp f₂ → RingHom.ker f₁ ⊓ RingHom.ker f₂ = ⊥ → IsNilpotent (RingHom.ker g₂) → IsNilpotent (RingHom.ker f₁) := by
  intro P R₁ R₂ R₀ _ _ _ _ f₁ f₂ g₁ g₂ w hj hn
  obtain ⟨n, hn⟩ := hn
  refine ⟨n + 1, ?_⟩
  rw [Submodule.zero_eq_bot, eq_bot_iff]
  intro x hx
  have h1 : x ∈ RingHom.ker f₁ := Ideal.pow_le_self (Nat.succ_ne_zero n) hx
  have hle : (RingHom.ker f₁).map f₂ ≤ RingHom.ker g₂ := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, ← w, RingHom.comp_apply,
      (RingHom.mem_ker).mp hy, map_zero]
  have h2 : f₂ x ∈ (RingHom.ker g₂) ^ (n + 1) := by
    have := Ideal.mem_map_of_mem f₂ hx
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle _ this
  rw [pow_succ, hn, Submodule.zero_eq_bot, Submodule.bot_mul] at h2
  have h3 : x ∈ RingHom.ker f₁ ⊓ RingHom.ker f₂ := ⟨h1, by simpa using h2⟩
  rw [hj] at h3
  exact h3

/- English proof (translation)
The claim follows from `GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf`.
-/
theorem mul_injective_of_flat : ∀ (P R₂ B B₂ : Type) [CommRing P] [CommRing R₂] [CommRing B] [CommRing B₂] [Algebra P B] (K₁ : Ideal P) (f₂ : P →+* R₂) (a₂ : R₂ →+* B₂) (c₂ : B →+* B₂), Function.Surjective f₂ → Function.Surjective c₂ → c₂.comp (algebraMap P B) = a₂.comp f₂ → RingHom.ker c₂ = (RingHom.ker f₂).map (algebraMap P B) → K₁ ⊓ RingHom.ker f₂ = ⊥ → a₂.Flat → Function.Injective (TensorProduct.lift ((LinearMap.lsmul P B).comp K₁.subtype)) := GlobalTheory.T.mul_tensor_injective_of_flat_baseChange_ker_inf

/- English proof (translation)
The claim follows from `GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat`.
-/
theorem flat_quotient_of_flat : ∀ (P R₁ B B₁ : Type) [CommRing P] [CommRing R₁] [CommRing B] [CommRing B₁] [Algebra P B] (f₁ : P →+* R₁) (a₁ : R₁ →+* B₁) (c₁ : B →+* B₁), Function.Surjective f₁ → Function.Surjective c₁ → c₁.comp (algebraMap P B) = a₁.comp f₁ → RingHom.ker c₁ = (RingHom.ker f₁).map (algebraMap P B) → a₁.Flat → Module.Flat (P ⧸ RingHom.ker f₁) (B ⧸ (RingHom.ker f₁ • ⊤ : Submodule P B)) := GlobalTheory.T.flat_quotient_smul_top_of_surjective_flat

/- English proof (translation)
Introduce `P R₁ R₂ R₀ B₁ B₂ B₀ B f₁ f₂ g₁ g₂ a₁ a₂ a₀ b₁ b₂ c₁ c₂ a hP hg₁ hg₂ hn₁ hn₂ hA₁ hA₂ hfl₁ hfl₂ hB hac₁ hac₂`. Establish `eP` using `exists_unique_of_isPullback f₁ f₂ g₁ g₂ hP`. Establish `eB` using `exists_unique_of_isPullback c₁ c₂ b₁ b₂ hB`. Take `⟨hb₁, hkb₁⟩` from `surjective_ker_of_isPushout a₁ g₁ b₁ a₀ hA₁ hg₁`. Take `⟨hb₂, hkb₂⟩` from `surjective_ker_of_isPushout a₂ g₂ b₂ a₀ hA₂ hg₂`.

Establish `wP : g₁.hom.comp f₁.hom = g₂.hom.comp f₂.hom`. Rewrite using `[← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hP.w]`. Establish `wB : ∀ x, b₁.hom (c₁.hom x) = b₂.hom (c₂.hom x)` using `fun x => by`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hB.w]`. Establish `w₁ : c₁.hom.comp a.hom = a₁.hom.comp f₁.hom`.

Rewrite using `[← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₁]`. Establish `w₂ : c₂.hom.comp a.hom = a₂.hom.comp f₂.hom`. Rewrite using `[← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₂]`. Establish `sf₁ : Function.Surjective f₁.hom` using `fun x => by`. Take `⟨y, hy⟩` from `hg₂ (g₁.hom x)`.

Take `⟨p, hp, -⟩` from `eP x y hy.symm`. Conclude with `⟨p, hp.1⟩`. Establish `sf₂ : Function.Surjective f₂.hom` using `fun y => by`. Take `⟨x, hx⟩` from `hg₁ (g₂.hom y)`. Take `⟨p, hp, -⟩` from `eP x y hx`.

Conclude with `⟨p, hp.2⟩`. Establish `sc₁ : Function.Surjective c₁.hom` using `fun x => by`. Take `⟨y, hy⟩` from `hb₂ (b₁.hom x)`. Take `⟨p, hp, -⟩` from `eB x y hy.symm`. Conclude with `⟨p, hp.1⟩`.

Establish `sc₂ : Function.Surjective c₂.hom` using `fun y => by`. Take `⟨x, hx⟩` from `hb₁ (b₂.hom y)`. Take `⟨p, hp, -⟩` from `eB x y hx`. Conclude with `⟨p, hp.2⟩`. Establish `jB : ∀ x : B, c₁.hom x = 0 → c₂.hom x = 0 → x = 0` using `fun x h1 h2 => by`.

Take `⟨p, -, hu⟩` from `eB 0 0 (by simp)`. Rewrite using `[hu x ⟨h1, h2⟩, hu 0 ⟨by simp, by simp⟩]`. Establish `jP : RingHom.ker f₁.hom ⊓ RingHom.ker f₂.hom = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Take `⟨p, -, hu⟩` from `eP 0 0 (by simp)`. Rewrite using `[Ideal.mem_bot, hu x ⟨hx.1, hx.2⟩, hu 0 ⟨by simp, by simp⟩]`. Establish `kc₁ : RingHom.ker c₁.hom = (RingHom.ker f₁.hom).map a.hom` using `ker_eq_map_of_fibre P R₁ R₂ B B₁ B₂ f₁.hom f₂.hom a.hom a₁.hom a₂.hom c₁.hom c₂.hom (RingHom.ker g₂.hom) w₁ w₂ sc₂ (fun k hk => by`. Take `⟨p, hp, -⟩` from `eP 0 k (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk).symm)`. Conclude with `⟨p, hp.1, hp.2⟩) jB`.

Use the proof step `(fun x hx => by`. Rewrite using `[← hkb₂, RingHom.mem_ker, ← wB, hx, map_zero])`. Establish `kc₂ : RingHom.ker c₂.hom = (RingHom.ker f₂.hom).map a.hom` using `ker_eq_map_of_fibre P R₂ R₁ B B₂ B₁ f₂.hom f₁.hom a.hom a₂.hom a₁.hom c₂.hom c₁.hom (RingHom.ker g₁.hom) w₂ w₁ sc₁ (fun k hk => by`. Take `⟨p, hp, -⟩` from `eP k 0 (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk))`. Conclude with `⟨p, hp.2, hp.1⟩) (fun x h2 h1 => jB x h1 h2)`.

Use the proof step `(fun x hx => by`. Rewrite using `[← hkb₁, RingHom.mem_ker, wB, hx, map_zero])`. Establish `nil₁ : IsNilpotent (RingHom.ker f₁.hom)` using `isNilpotent_ker_of_fibre P R₁ R₂ R₀ f₁.hom f₂.hom g₁.hom g₂.hom wP jP hn₂`. Use `⟨?_, isPushout_of_surjective_of_ker a f₁ c₁ a₁ hac₁ sf₁ sc₁ kc₁, isPushout_of_surjective_of_ker a f₂ c₂ a₂ hac₂ sf₂ sc₂ kc₂⟩` and prove the remaining obligations. Use `letI : Algebra P B := a.hom.toAlgebra`.

Express the relevant statement in the definitionally equal form `Module.Flat P B`. Conclude with `GlobalTheory.NilpotentFlat.flat_of_isNilpotent P (RingHom.ker f₁.hom) nil₁ B (flat_quotient_of_flat P R₁ B B₁ f₁.hom a₁.hom c₁.hom sf₁ sc₁ w₁ kc₁ hfl₁) (mul_injective_of_flat P R₂ B B₂ (RingHom.ker f₁.hom) f₂.hom a₂.hom c₂.hom sf₂ sc₂ w₂ kc₂ jP hfl₂)`.
-/
theorem schlessinger_flat : ∀ (P R₁ R₂ R₀ B₁ B₂ B₀ B : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀) (a₁ : R₁ ⟶ B₁) (a₂ : R₂ ⟶ B₂) (a₀ : R₀ ⟶ B₀) (b₁ : B₁ ⟶ B₀) (b₂ : B₂ ⟶ B₀) (c₁ : B ⟶ B₁) (c₂ : B ⟶ B₂) (a : P ⟶ B), IsPullback f₁ f₂ g₁ g₂ → Function.Surjective g₁ → Function.Surjective g₂ → IsNilpotent (RingHom.ker g₁.hom) → IsNilpotent (RingHom.ker g₂.hom) → IsPushout a₁ g₁ b₁ a₀ → IsPushout a₂ g₂ b₂ a₀ → a₁.hom.Flat → a₂.hom.Flat → IsPullback c₁ c₂ b₁ b₂ → a ≫ c₁ = f₁ ≫ a₁ → a ≫ c₂ = f₂ ≫ a₂ → a.hom.Flat ∧ IsPushout a f₁ c₁ a₁ ∧ IsPushout a f₂ c₂ a₂ := by
  intro P R₁ R₂ R₀ B₁ B₂ B₀ B f₁ f₂ g₁ g₂ a₁ a₂ a₀ b₁ b₂ c₁ c₂ a hP hg₁ hg₂ hn₁ hn₂ hA₁ hA₂ hfl₁ hfl₂ hB hac₁ hac₂
  have eP := exists_unique_of_isPullback f₁ f₂ g₁ g₂ hP
  have eB := exists_unique_of_isPullback c₁ c₂ b₁ b₂ hB
  obtain ⟨hb₁, hkb₁⟩ := surjective_ker_of_isPushout a₁ g₁ b₁ a₀ hA₁ hg₁
  obtain ⟨hb₂, hkb₂⟩ := surjective_ker_of_isPushout a₂ g₂ b₂ a₀ hA₂ hg₂
  have wP : g₁.hom.comp f₁.hom = g₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hP.w]
  have wB : ∀ x, b₁.hom (c₁.hom x) = b₂.hom (c₂.hom x) := fun x => by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, hB.w]
  have w₁ : c₁.hom.comp a.hom = a₁.hom.comp f₁.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₁]
  have w₂ : c₂.hom.comp a.hom = a₂.hom.comp f₂.hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, hac₂]
  have sf₁ : Function.Surjective f₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hg₂ (g₁.hom x)
    obtain ⟨p, hp, -⟩ := eP x y hy.symm
    exact ⟨p, hp.1⟩
  have sf₂ : Function.Surjective f₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hg₁ (g₂.hom y)
    obtain ⟨p, hp, -⟩ := eP x y hx
    exact ⟨p, hp.2⟩
  have sc₁ : Function.Surjective c₁.hom := fun x => by
    obtain ⟨y, hy⟩ := hb₂ (b₁.hom x)
    obtain ⟨p, hp, -⟩ := eB x y hy.symm
    exact ⟨p, hp.1⟩
  have sc₂ : Function.Surjective c₂.hom := fun y => by
    obtain ⟨x, hx⟩ := hb₁ (b₂.hom y)
    obtain ⟨p, hp, -⟩ := eB x y hx
    exact ⟨p, hp.2⟩
  have jB : ∀ x : B, c₁.hom x = 0 → c₂.hom x = 0 → x = 0 := fun x h1 h2 => by
    obtain ⟨p, -, hu⟩ := eB 0 0 (by simp)
    rw [hu x ⟨h1, h2⟩, hu 0 ⟨by simp, by simp⟩]
  have jP : RingHom.ker f₁.hom ⊓ RingHom.ker f₂.hom = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨p, -, hu⟩ := eP 0 0 (by simp)
    rw [Ideal.mem_bot, hu x ⟨hx.1, hx.2⟩, hu 0 ⟨by simp, by simp⟩]
  have kc₁ : RingHom.ker c₁.hom = (RingHom.ker f₁.hom).map a.hom :=
    ker_eq_map_of_fibre P R₁ R₂ B B₁ B₂ f₁.hom f₂.hom a.hom a₁.hom a₂.hom c₁.hom c₂.hom (RingHom.ker g₂.hom) w₁ w₂ sc₂
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP 0 k (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk).symm)
        exact ⟨p, hp.1, hp.2⟩) jB
      (fun x hx => by
        rw [← hkb₂, RingHom.mem_ker, ← wB, hx, map_zero])
  have kc₂ : RingHom.ker c₂.hom = (RingHom.ker f₂.hom).map a.hom :=
    ker_eq_map_of_fibre P R₂ R₁ B B₂ B₁ f₂.hom f₁.hom a.hom a₂.hom a₁.hom c₂.hom c₁.hom (RingHom.ker g₁.hom) w₂ w₁ sc₁
      (fun k hk => by
        obtain ⟨p, hp, -⟩ := eP k 0 (by rw [map_zero]; exact ((RingHom.mem_ker).mp hk))
        exact ⟨p, hp.2, hp.1⟩) (fun x h2 h1 => jB x h1 h2)
      (fun x hx => by
        rw [← hkb₁, RingHom.mem_ker, wB, hx, map_zero])
  have nil₁ : IsNilpotent (RingHom.ker f₁.hom) :=
    isNilpotent_ker_of_fibre P R₁ R₂ R₀ f₁.hom f₂.hom g₁.hom g₂.hom wP jP hn₂
  refine ⟨?_, isPushout_of_surjective_of_ker a f₁ c₁ a₁ hac₁ sf₁ sc₁ kc₁, isPushout_of_surjective_of_ker a f₂ c₂ a₂ hac₂ sf₂ sc₂ kc₂⟩
  letI : Algebra P B := a.hom.toAlgebra
  change Module.Flat P B
  exact GlobalTheory.NilpotentFlat.flat_of_isNilpotent P (RingHom.ker f₁.hom) nil₁ B
    (flat_quotient_of_flat P R₁ B B₁ f₁.hom a₁.hom c₁.hom sf₁ sc₁ w₁ kc₁ hfl₁)
    (mul_injective_of_flat P R₂ B B₂ (RingHom.ker f₁.hom) f₂.hom a₂.hom c₂.hom sf₂ sc₂ w₂ kc₂ jP hfl₂)

end GlobalTheory.SchlessingerFlat
