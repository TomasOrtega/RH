import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XDotdualBc
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XGraphRestrictBc
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.LocallyFreeLatticeSpans

open PositivityTheory.Xgn.A_graph_restrict_bc

section Free

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
  {V Z : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Z] [Module Ω Z]

/- English proof (translation)
Simplify using `[stdLat, AddSubgroup.mem_pi]`.
-/
theorem mem_std {ι : Type} (v : ι → Ω) : v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_div (c : Ω) (L : AddSubgroup V) (v : V) : v ∈ divLat c L ↔ c • v ∈ L := Iff.rfl

/- English proof (translation)
Use `⟨fun a ha e he => (mem_std R _).2 fun i => R.mul_mem ha ((mem_std R _).1 he i), 1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp, fun _ => ?_⟩` and prove the remaining obligations. Use `⟨Pi.basisFun Ω (Fin n), (Pi.basisFun Ω (Fin n)).linearIndependent, (Pi.basisFun Ω (Fin n)).span_eq, fun e => ?_⟩` and prove the remaining obligations. Establish `h : ∀ a : Fin n → Ω, ∑ q, a q • Pi.basisFun Ω (Fin n) q = a` using `fun a => by`. Simplify using `using (Pi.basisFun Ω (Fin n)).sum_repr a`. Simplify using `only [one_pow, one_smul, one_mul, exists_const, h, mem_std]`.

Conclude with `⟨fun he => ⟨e, he, rfl⟩, fun ⟨a, ha, he⟩ => he ▸ ha⟩`.
-/
theorem locFree_std (n : ℕ) : LocFree R n (stdLat R (Fin n)) := by
  refine ⟨fun a ha e he => (mem_std R _).2 fun i => R.mul_mem ha ((mem_std R _).1 he i),
    1, fun _ => 1, fun _ => 1, fun _ => R.one_mem, fun _ => R.one_mem, by simp, fun _ => ?_⟩
  refine ⟨Pi.basisFun Ω (Fin n), (Pi.basisFun Ω (Fin n)).linearIndependent,
    (Pi.basisFun Ω (Fin n)).span_eq, fun e => ?_⟩
  have h : ∀ a : Fin n → Ω, ∑ q, a q • Pi.basisFun Ω (Fin n) q = a := fun a => by
    simpa using (Pi.basisFun Ω (Fin n)).sum_repr a
  simp only [one_pow, one_smul, one_mul, exists_const, h, mem_std]
  exact ⟨fun he => ⟨e, he, rfl⟩, fun ⟨a, ha, he⟩ => he ▸ ha⟩

/- English proof (translation)
Take `⟨hst, k, f, d, hf, hd, hsum, hloc⟩` from `h`. Use `⟨fun a ha e he => ?_, k, f, d, hf, hd, hsum, fun l => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_div, smul_comm]`. Conclude with `hst a ha _ he`. Take `⟨b, hli, hsp, hb⟩` from `hloc l`.

Set `B : Module.Basis (Fin r) Ω V` to `Module.Basis.mk hli hsp.ge`. Set `B' : Module.Basis (Fin r) Ω V` to `B.unitsSMul fun _ => (Units.mk0 c hc)⁻¹`. Establish `hB' : ∀ q, B' q = c⁻¹ • b q` using `fun q => by`. Simplify using `[B', B, Module.Basis.unitsSMul_apply, Units.smul_def]`. Use `⟨B', B'.linearIndependent, B'.span_eq, fun e => ?_⟩` and prove the remaining obligations.

Establish `h1 : (∃ n : ℕ, f l ^ n • e ∈ divLat c L) ↔ ∃ n : ℕ, f l ^ n • (c • e) ∈ L` using `exists_congr fun n => by rw [mem_div, smul_comm]`. Rewrite using `[h1, hb]`. Use `exists_congr fun a => and_congr Iff.rfl ?_` and prove the remaining obligations. Establish `h2 : ∑ q, a q • B' q = c⁻¹ • ∑ q, a q • b q`. Rewrite using `[Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl fun q _ => by rw [hB', smul_comm]`. Rewrite using `[h2, eq_inv_smul_iff₀ hc]`.
-/
theorem locFree_div {c : Ω} (hc : c ≠ 0) {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    LocFree R r (divLat c L) := by
  obtain ⟨hst, k, f, d, hf, hd, hsum, hloc⟩ := h
  refine ⟨fun a ha e he => ?_, k, f, d, hf, hd, hsum, fun l => ?_⟩
  · rw [mem_div, smul_comm]
    exact hst a ha _ he
  obtain ⟨b, hli, hsp, hb⟩ := hloc l
  let B : Module.Basis (Fin r) Ω V := Module.Basis.mk hli hsp.ge
  let B' : Module.Basis (Fin r) Ω V := B.unitsSMul fun _ => (Units.mk0 c hc)⁻¹
  have hB' : ∀ q, B' q = c⁻¹ • b q := fun q => by
    simp [B', B, Module.Basis.unitsSMul_apply, Units.smul_def]
  refine ⟨B', B'.linearIndependent, B'.span_eq, fun e => ?_⟩
  have h1 : (∃ n : ℕ, f l ^ n • e ∈ divLat c L) ↔ ∃ n : ℕ, f l ^ n • (c • e) ∈ L :=
    exists_congr fun n => by rw [mem_div, smul_comm]
  rw [h1, hb]
  refine exists_congr fun a => and_congr Iff.rfl ?_
  have h2 : ∑ q, a q • B' q = c⁻¹ • ∑ q, a q • b q := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [hB', smul_comm]
  rw [h2, eq_inv_smul_iff₀ hc]

/- English proof (translation)
Set `L' : Submodule R V` to `{ L with smul_mem' := fun a e he => hL.1 a a.2 e he }`. Take `⟨k, φ, v, hφ, hv⟩` from `LocFreeProj.exists_dualBasis (L := L') (r := N) hL`. Establish `hz : ∀ i, ∃ e ∈ Δ, q e = π (v i)` using `fun i => h _ (v i).2`. Use `choose z hz hz' using hz`. Use `⟨∑ i, (φ i).smulRight (z i), fun x => ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← hv x]`. Simplify using `[map_sum, hz']`. Simplify using `only [LinearMap.sum_apply, LinearMap.smulRight_apply]`. Conclude with `AddSubgroup.sum_mem _ fun i _ => hΔ _ (hφ i x hx) _ (hz i)`.
-/
theorem exists_lift {E : Type} [AddCommGroup E] [Module Ω E] (Δ : AddSubgroup E)
    (hΔ : ∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) (q : E →ₗ[Ω] V) (π : V →ₗ[Ω] V) {N : ℕ}
    (L : AddSubgroup V) (hL : LocFree R N L) (h : ∀ v ∈ L, ∃ e ∈ Δ, q e = π v) :
    ∃ σ : V →ₗ[Ω] E, (∀ v, q (σ v) = π v) ∧ ∀ v ∈ L, σ v ∈ Δ := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => hL.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := N) hL
  have hz : ∀ i, ∃ e ∈ Δ, q e = π (v i) := fun i => h _ (v i).2
  choose z hz hz' using hz
  refine ⟨∑ i, (φ i).smulRight (z i), fun x => ?_, fun x hx => ?_⟩
  · conv_rhs => rw [← hv x]
    simp [map_sum, hz']
  · simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
    exact AddSubgroup.sum_mem _ fun i _ => hΔ _ (hφ i x hx) _ (hz i)

/- English proof (translation)
Take `⟨σ, h1, h2⟩` from `exists_lift R Δ hΔ (LinearMap.fst Ω V Z) π L hL fun v hv => by`. Take `⟨z, hz⟩` from `h v hv`. Conclude with `⟨_, hz, rfl⟩`. Use `⟨LinearMap.snd Ω V Z ∘ₗ σ, fun v z hvz => ?_⟩` and prove the remaining obligations. Take `⟨h3, h4⟩` from `h' v z hvz`.

Establish `h5 : (σ v).1 = v` using `(h1 v).trans h4`. Establish `h6` using `h2 v h3`. Rewrite `h6` using `[← Prod.mk.eta (p := σ v), h5]`. Conclude with `h6`.
-/
theorem sec_fst (Δ : AddSubgroup (V × Z)) (hΔ : ∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) (π : V →ₗ[Ω] V)
    {N : ℕ} (L : AddSubgroup V) (hL : LocFree R N L) (h : ∀ v ∈ L, ∃ z, (π v, z) ∈ Δ)
    (h' : ∀ v z, (v, z) ∈ Δ → v ∈ L ∧ π v = v) :
    ∃ σ : V →ₗ[Ω] Z, ∀ v z, (v, z) ∈ Δ → (v, σ v) ∈ Δ := by
  obtain ⟨σ, h1, h2⟩ := exists_lift R Δ hΔ (LinearMap.fst Ω V Z) π L hL fun v hv => by
    obtain ⟨z, hz⟩ := h v hv
    exact ⟨_, hz, rfl⟩
  refine ⟨LinearMap.snd Ω V Z ∘ₗ σ, fun v z hvz => ?_⟩
  obtain ⟨h3, h4⟩ := h' v z hvz
  have h5 : (σ v).1 = v := (h1 v).trans h4
  have h6 := h2 v h3
  rw [← Prod.mk.eta (p := σ v), h5] at h6
  exact h6

/- English proof (translation)
Take `⟨σ, h1, h2⟩` from `exists_lift R Δ hΔ (LinearMap.snd Ω V Z) LinearMap.id L hL fun z hz => by`. Take `⟨v, hv⟩` from `(h z).2 hz`. Conclude with `⟨_, hv, rfl⟩`. Use `⟨LinearMap.fst Ω V Z ∘ₗ σ, fun v z hvz => ?_⟩` and prove the remaining obligations. Establish `h5 : (σ z).2 = z` using `h1 z`.

Establish `h6` using `h2 z ((h z).1 ⟨v, hvz⟩)`. Rewrite `h6` using `[← Prod.mk.eta (p := σ z), h5]`. Conclude with `h6`.
-/
theorem sec_snd (Δ : AddSubgroup (V × Z)) (hΔ : ∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ)
    {N : ℕ} (L : AddSubgroup Z) (hL : LocFree R N L) (h : ∀ z, (∃ v, (v, z) ∈ Δ) ↔ z ∈ L) :
    ∃ σ : Z →ₗ[Ω] V, ∀ v z, (v, z) ∈ Δ → (σ z, z) ∈ Δ := by
  obtain ⟨σ, h1, h2⟩ := exists_lift R Δ hΔ (LinearMap.snd Ω V Z) LinearMap.id L hL fun z hz => by
    obtain ⟨v, hv⟩ := (h z).2 hz
    exact ⟨_, hv, rfl⟩
  refine ⟨LinearMap.fst Ω V Z ∘ₗ σ, fun v z hvz => ?_⟩
  have h5 : (σ z).2 = z := h1 z
  have h6 := h2 z ((h z).1 ⟨v, hvz⟩)
  rw [← Prod.mk.eta (p := σ z), h5] at h6
  exact h6

end Free

section Span

variable {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C]
  (RC : Subalgebra o C)
  {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc]
  [IsScalarTower Ω C Vc]
  {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc]
  [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc)

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, hc, e, he, rfl⟩` from `hy`. Take `⟨x, hx, rfl⟩` from `h e he`. Conclude with `⟨c • x, smul_mem hc (mem_span hx), map_smul _ _ _⟩`.

Consider the case `zero => exact ⟨0, AddSubgroup.zero_mem _, map_zero _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨x, hx, rfl⟩` from `hx`. Take `⟨y, hy, rfl⟩` from `hy`. Conclude with `⟨x + y, AddSubgroup.add_mem _ hx hy, map_add _ _ _⟩`.

Consider the case `neg x _ hx`. Take `⟨x, hx, rfl⟩` from `hx`. Conclude with `⟨-x, AddSubgroup.neg_mem _ hx, map_neg _ _⟩`.
-/
theorem exists_of_map {A B : Type} [AddCommGroup A] [Module C A] [AddCommGroup B] [Module C B]
    (T : A →ₗ[C] B) {S : Set A} {S' : Set B} (h : ∀ e ∈ S', ∃ x ∈ S, T x = e)
    {y : B} (hy : y ∈ spanOver RC S') : ∃ x ∈ spanOver RC S, T x = y := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, e, he, rfl⟩ := hy
    obtain ⟨x, hx, rfl⟩ := h e he
    exact ⟨c • x, smul_mem hc (mem_span hx), map_smul _ _ _⟩
  | zero => exact ⟨0, AddSubgroup.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact ⟨x + y, AddSubgroup.add_mem _ hx hy, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    exact ⟨-x, AddSubgroup.neg_mem _ hx, map_neg _ _⟩

omit [Algebra Ω C] [IsScalarTower Ω C Vc] [IsScalarTower Ω C Zc] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `map_mem (LinearMap.fst C Vc Zc) ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨v, z⟩, hv, rfl⟩`. Conclude with `mem_span ⟨v, (h v).1 ⟨z, hv⟩, rfl⟩`.

Introduce `hx`. Take `⟨⟨x', y⟩, hy, rfl⟩` from `exists_of_map RC (LinearMap.fst C Vc Zc) (S := Prod.map b b' '' Δ) (by`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Take `⟨z, hz⟩` from `(h v).2 hv`. Conclude with `⟨_, ⟨_, hz, rfl⟩, rfl⟩) hx`.

Conclude with `⟨y, hy⟩`.
-/
theorem span_fst (Δ : AddSubgroup (V × Z)) (S : Set V) (h : ∀ v, (∃ z, (v, z) ∈ Δ) ↔ v ∈ S) (x : Vc) :
    (∃ y, (x, y) ∈ spanOver RC (Prod.map b b' '' Δ)) ↔ x ∈ spanOver RC (b '' S) := by
  constructor
  · rintro ⟨y, hy⟩
    refine map_mem (LinearMap.fst C Vc Zc) ?_ hy
    rintro _ ⟨⟨v, z⟩, hv, rfl⟩
    exact mem_span ⟨v, (h v).1 ⟨z, hv⟩, rfl⟩
  · intro hx
    obtain ⟨⟨x', y⟩, hy, rfl⟩ := exists_of_map RC (LinearMap.fst C Vc Zc)
      (S := Prod.map b b' '' Δ) (by
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨z, hz⟩ := (h v).2 hv
        exact ⟨_, ⟨_, hz, rfl⟩, rfl⟩) hx
    exact ⟨y, hy⟩

omit [Algebra Ω C] [IsScalarTower Ω C Vc] [IsScalarTower Ω C Zc] in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`. Use `map_mem (LinearMap.snd C Vc Zc) ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨v, z⟩, hv, rfl⟩`. Conclude with `mem_span ⟨z, (h z).1 ⟨v, hv⟩, rfl⟩`.

Introduce `hy`. Take `⟨⟨x, y'⟩, hx, rfl⟩` from `exists_of_map RC (LinearMap.snd C Vc Zc) (S := Prod.map b b' '' Δ) (by`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨v, hv⟩` from `(h z).2 hz`. Conclude with `⟨_, ⟨_, hv, rfl⟩, rfl⟩) hy`.

Conclude with `⟨x, hx⟩`.
-/
theorem span_snd (Δ : AddSubgroup (V × Z)) (S : Set Z) (h : ∀ z, (∃ v, (v, z) ∈ Δ) ↔ z ∈ S) (y : Zc) :
    (∃ x, (x, y) ∈ spanOver RC (Prod.map b b' '' Δ)) ↔ y ∈ spanOver RC (b' '' S) := by
  constructor
  · rintro ⟨x, hx⟩
    refine map_mem (LinearMap.snd C Vc Zc) ?_ hx
    rintro _ ⟨⟨v, z⟩, hv, rfl⟩
    exact mem_span ⟨z, (h z).1 ⟨v, hv⟩, rfl⟩
  · intro hy
    obtain ⟨⟨x, y'⟩, hx, rfl⟩ := exists_of_map RC (LinearMap.snd C Vc Zc)
      (S := Prod.map b b' '' Δ) (by
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨v, hv⟩ := (h z).2 hz
        exact ⟨_, ⟨_, hv, rfl⟩, rfl⟩) hy
    exact ⟨x, hx⟩

/- English proof (translation)
Take `⟨σ, hσ⟩` from `hσ`. Take `⟨τ, hτ⟩ : ∃ τ : Vc →ₗ[C] Zc, ∀ v, τ (b v) = b' (σ v)` from `⟨hb.lift (b' ∘ₗ σ), fun v => hb.lift_eq _ v⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `map_mem (LinearMap.snd C Vc Zc - τ ∘ₗ LinearMap.fst C Vc Zc) (S' := b' '' K) ?_ hy` as an intermediate fact.

Simplify using `using this`. Introduce and unpack `_ ⟨⟨v, z⟩, hvz, rfl⟩`. Use `mem_span ⟨z - σ v, (hK _).1 ?_, by simp [hτ]⟩` and prove the remaining obligations. Simplify using `using Δ.sub_mem hvz (hσ v z hvz)`. Introduce `hy`.

Use `map_mem (LinearMap.inr C Vc Zc) ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `mem_span ⟨(0, v), (hK v).2 hv, by simp⟩`.
-/
theorem span_ker_fst (hb : IsBaseChange C b) (Δ : AddSubgroup (V × Z))
    (hσ : ∃ σ : V →ₗ[Ω] Z, ∀ v z, (v, z) ∈ Δ → (v, σ v) ∈ Δ) (K : Set Z)
    (hK : ∀ z, (0, z) ∈ Δ ↔ z ∈ K) (y : Zc) :
    (0, y) ∈ spanOver RC (Prod.map b b' '' Δ) ↔ y ∈ spanOver RC (b' '' K) := by
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨τ, hτ⟩ : ∃ τ : Vc →ₗ[C] Zc, ∀ v, τ (b v) = b' (σ v) :=
    ⟨hb.lift (b' ∘ₗ σ), fun v => hb.lift_eq _ v⟩
  constructor
  · intro hy
    have := map_mem (LinearMap.snd C Vc Zc - τ ∘ₗ LinearMap.fst C Vc Zc) (S' := b' '' K) ?_ hy
    · simpa using this
    rintro _ ⟨⟨v, z⟩, hvz, rfl⟩
    refine mem_span ⟨z - σ v, (hK _).1 ?_, by simp [hτ]⟩
    simpa using Δ.sub_mem hvz (hσ v z hvz)
  · intro hy
    refine map_mem (LinearMap.inr C Vc Zc) ?_ hy
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨(0, v), (hK v).2 hv, by simp⟩

/- English proof (translation)
Take `⟨σ, hσ⟩` from `hσ`. Take `⟨τ, hτ⟩ : ∃ τ : Zc →ₗ[C] Vc, ∀ v, τ (b' v) = b (σ v)` from `⟨hb.lift (b ∘ₗ σ), fun v => hb.lift_eq _ v⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Use `map_mem (LinearMap.fst C Vc Zc - τ ∘ₗ LinearMap.snd C Vc Zc) (S' := b '' K) ?_ hy` as an intermediate fact.

Simplify using `using this`. Introduce and unpack `_ ⟨⟨v, z⟩, hvz, rfl⟩`. Use `mem_span ⟨v - σ z, (hK _).1 ?_, by simp [hτ]⟩` and prove the remaining obligations. Simplify using `using Δ.sub_mem hvz (hσ v z hvz)`. Introduce `hy`.

Use `map_mem (LinearMap.inl C Vc Zc) ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `mem_span ⟨(v, 0), (hK v).2 hv, by simp⟩`.
-/
theorem span_ker_snd (hb : IsBaseChange C b') (Δ : AddSubgroup (V × Z))
    (hσ : ∃ σ : Z →ₗ[Ω] V, ∀ v z, (v, z) ∈ Δ → (σ z, z) ∈ Δ) (K : Set V)
    (hK : ∀ v, (v, 0) ∈ Δ ↔ v ∈ K) (x : Vc) :
    (x, 0) ∈ spanOver RC (Prod.map b b' '' Δ) ↔ x ∈ spanOver RC (b '' K) := by
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨τ, hτ⟩ : ∃ τ : Zc →ₗ[C] Vc, ∀ v, τ (b' v) = b (σ v) :=
    ⟨hb.lift (b ∘ₗ σ), fun v => hb.lift_eq _ v⟩
  constructor
  · intro hy
    have := map_mem (LinearMap.fst C Vc Zc - τ ∘ₗ LinearMap.snd C Vc Zc) (S' := b '' K) ?_ hy
    · simpa using this
    rintro _ ⟨⟨v, z⟩, hvz, rfl⟩
    refine mem_span ⟨v - σ z, (hK _).1 ?_, by simp [hτ]⟩
    simpa using Δ.sub_mem hvz (hσ v z hvz)
  · intro hy
    refine map_mem (LinearMap.inl C Vc Zc) ?_ hy
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨(v, 0), (hK v).2 hv, by simp⟩

/- English proof (translation)
Establish `hc' : algebraMap Ω C c ≠ 0` using `by simpa using hc`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `map_mem (algebraMap Ω C c • LinearMap.id) ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Conclude with `mem_span ⟨c • v, hv, by simp⟩`. Introduce `hx`. Use `map_mem ((algebraMap Ω C c)⁻¹ • LinearMap.id) (S' := b '' divLat c L) ?_ hx` as an intermediate fact. Simplify `this` using `only [LinearMap.smul_apply, LinearMap.id_apply, inv_smul_smul₀ hc']`. Introduce and unpack `_ ⟨v, hv, rfl⟩`.

Use `mem_span ⟨c⁻¹ • v, ?_, by simp [← map_inv₀]⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c • c⁻¹ • v ∈ L`. Rewrite using `[smul_inv_smul₀ hc]` and apply the resulting hypothesis.
-/
theorem span_div {c : Ω} (hc : c ≠ 0) (L : AddSubgroup V) (x : Vc) :
    x ∈ spanOver RC (b '' divLat c L) ↔ algebraMap Ω C c • x ∈ spanOver RC (b '' L) := by
  have hc' : algebraMap Ω C c ≠ 0 := by simpa using hc
  constructor
  · intro hx
    refine map_mem (algebraMap Ω C c • LinearMap.id) ?_ hx
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨c • v, hv, by simp⟩
  · intro hx
    have := map_mem ((algebraMap Ω C c)⁻¹ • LinearMap.id) (S' := b '' divLat c L) ?_ hx
    · simpa only [LinearMap.smul_apply, LinearMap.id_apply, inv_smul_smul₀ hc'] using this
    rintro _ ⟨v, hv, rfl⟩
    refine mem_span ⟨c⁻¹ • v, ?_, by simp [← map_inv₀]⟩
    change c • c⁻¹ • v ∈ L
    rwa [smul_inv_smul₀ hc]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `exists_of_map RC (algebraMap Ω C c • LinearMap.id) ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨v, hv, rfl⟩, rfl⟩`. Conclude with `⟨b v, ⟨v, hv, rfl⟩, by simp⟩`.

Introduce and unpack `⟨y, hy, rfl⟩`. Use `map_mem (algebraMap Ω C c • LinearMap.id) ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `mem_span ⟨c • v, ⟨v, hv, rfl⟩, by simp⟩`.
-/
theorem span_mul (c : Ω) (L : AddSubgroup V) (x : Vc) :
    x ∈ spanOver RC (b '' mulLat c L) ↔
      x ∈ mulLat (algebraMap Ω C c) (spanOver RC (b '' L)) := by
  constructor
  · intro hx
    refine exists_of_map RC (algebraMap Ω C c • LinearMap.id) ?_ hx
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨b v, ⟨v, hv, rfl⟩, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    refine map_mem (algebraMap Ω C c • LinearMap.id) ?_ hy
    rintro _ ⟨v, hv, rfl⟩
    exact mem_span ⟨c • v, ⟨v, hv, rfl⟩, by simp⟩

omit [Algebra Ω C] [IsScalarTower Ω C Vc] in
/- English proof (translation)
Introduce `x hx`. Use `map_mem LinearMap.id ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `mem_span ⟨v, h hv, rfl⟩`.
-/
theorem span_mono {L L' : AddSubgroup V} (h : L ≤ L') :
    spanOver RC (b '' L) ≤ spanOver RC (b '' L') := by
  intro x hx
  refine map_mem LinearMap.id ?_ hx
  rintro _ ⟨v, hv, rfl⟩
  exact mem_span ⟨v, h hv, rfl⟩

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Apply `le_antisymm` to reduce the goal to its premises. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩`. Conclude with `(mem_std RC _).2 fun i => RC.mul_mem ha (hR _ ((mem_std R _).1 hv i))`.

Introduce `x hx`. Establish `h1 : x = ∑ i, x i • bcMap Ω C ι (Pi.single i 1)`. Use function extensionality and compare the values at `j`. Establish `h2 : ∀ i, bcMap Ω C ι (Pi.single i 1) j = if j = i then 1 else 0` using `fun i => by`. Express the relevant statement in the definitionally equal form `algebraMap Ω C ((Pi.single i 1 : ι → Ω) j) = _`.

Rewrite using `[Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `[Finset.sum_apply, h2]`. Rewrite using `[h1]`. Use `AddSubgroup.sum_mem _ fun i _ => smul_mem ((mem_std RC _).1 hx i) (mem_span ⟨_, (mem_std R _).2 fun j => ?_, rfl⟩)` and prove the remaining obligations.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `R.zero_mem`.
-/
theorem span_std [Algebra o Ω] (R : Subalgebra o Ω) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    (ι : Type) [Finite ι] : spanOver RC (bcMap Ω C ι '' stdLat R ι) = stdLat RC ι := by
  classical
  have := Fintype.ofFinite ι
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, _, ⟨v, hv, rfl⟩, rfl⟩
    exact (mem_std RC _).2 fun i => RC.mul_mem ha (hR _ ((mem_std R _).1 hv i))
  · intro x hx
    have h1 : x = ∑ i, x i • bcMap Ω C ι (Pi.single i 1) := by
      funext j
      have h2 : ∀ i, bcMap Ω C ι (Pi.single i 1) j = if j = i then 1 else 0 := fun i => by
        change algebraMap Ω C ((Pi.single i 1 : ι → Ω) j) = _
        rw [Pi.single_apply]
        split_ifs <;> simp
      simp [Finset.sum_apply, h2]
    rw [h1]
    refine AddSubgroup.sum_mem _ fun i _ => smul_mem ((mem_std RC _).1 hx i)
      (mem_span ⟨_, (mem_std R _).2 fun j => ?_, rfl⟩)
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem

/- English proof (translation)
The claim follows from `IsBaseChange.finitePow ι (IsBaseChange.linearMap Ω C)`.
-/
theorem isBC (Ω C : Type) [Field Ω] [Field C] [Algebra Ω C] (ι : Type) [Finite ι] :
    IsBaseChange C (bcMap Ω C ι) :=
  IsBaseChange.finitePow ι (IsBaseChange.linearMap Ω C)

end Span

noncomputable def aug (Ω : Type) [Field Ω] {ι : Type} (x₀ : ι) : (ι → Ω) →ₗ[Ω] (ι → Ω) :=
  LinearMap.id - (LinearMap.proj x₀ : (ι → Ω) →ₗ[Ω] Ω).smulRight 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem aug_apply {Ω : Type} [Field Ω] {ι : Type} (x₀ : ι) (g : ι → Ω) :
    aug Ω x₀ g = g - g x₀ • (1 : ι → Ω) := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨map_mem LinearMap.id ?_ hx, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Conclude with `mem_span ⟨v, hv.1, rfl⟩`.

Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨c, -, _, ⟨v, hv, rfl⟩, rfl⟩` from `hy`. Express the relevant statement in the definitionally equal form `c * algebraMap Ω C (v x₀) = 0`. Rewrite using `[hv.2, map_zero, mul_zero]`.

Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]`. Consider the case `neg x _ hx => rw [Pi.neg_apply, hx, neg_zero]`. Introduce and unpack `⟨hx, h0⟩`. Use `map_mem (aug C x₀) (S' := bcMap Ω C ι '' {g | g ∈ M ∧ g x₀ = 0}) ?_ hx` as an intermediate fact.

Simplify `this` using `[aug_apply, h0]`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Use `mem_span ⟨aug Ω x₀ v, ⟨hM v hv, by simp [aug_apply]⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Simplify using `[aug_apply, bcMap, Algebra.algebraMap_eq_smul_one, sub_smul]`.
-/
theorem span_aug {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o C] [Algebra Ω C]
    (RC : Subalgebra o C) {ι : Type} (x₀ : ι) (M : AddSubgroup (ι → Ω))
    (hM : ∀ g ∈ M, aug Ω x₀ g ∈ M) (x : ι → C) :
    x ∈ spanOver RC (bcMap Ω C ι '' {g | g ∈ M ∧ g x₀ = 0}) ↔
      x ∈ spanOver RC (bcMap Ω C ι '' M) ∧ x x₀ = 0 := by
  constructor
  · intro hx
    refine ⟨map_mem LinearMap.id ?_ hx, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact mem_span ⟨v, hv.1, rfl⟩
    · induction hx using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨c, -, _, ⟨v, hv, rfl⟩, rfl⟩ := hy
        change c * algebraMap Ω C (v x₀) = 0
        rw [hv.2, map_zero, mul_zero]
      | zero => rfl
      | add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]
      | neg x _ hx => rw [Pi.neg_apply, hx, neg_zero]
  · rintro ⟨hx, h0⟩
    have := map_mem (aug C x₀) (S' := bcMap Ω C ι '' {g | g ∈ M ∧ g x₀ = 0}) ?_ hx
    · simpa [aug_apply, h0] using this
    rintro _ ⟨v, hv, rfl⟩
    refine mem_span ⟨aug Ω x₀ v, ⟨hM v hv, by simp [aug_apply]⟩, ?_⟩
    funext j
    simp [aug_apply, bcMap, Algebra.algebraMap_eq_smul_one, sub_smul]

section Clauses

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [Fintype F] {n : ℕ}
  {Sg : Type} {r s : Sg → ℕ} {D : LieLatticeData Ω F n Sg r s} {R : Subalgebra o Ω} {p : ℕ} {w : Ω}
  {C : Type} [Field C] [Algebra o C] [Algebra Ω C] {RC : Subalgebra o C}

/- English proof (translation)
Establish `hstd` using `locFree_div R hw0 (locFree_std R n)`. Take `⟨g1, g2, g3⟩` from `hD.gam τ`. Take `⟨d1, d2, d3, d4⟩` from `hD.del τ`. Take `⟨-, fW, -, fH⟩` from `hD.free τ`. Establish `sG : ∀ a ∈ R, ∀ v ∈ D.Gam τ, a • v ∈ D.Gam τ` using `fun a ha => (hD.stable τ a ha).1`.

Establish `sD : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ` using `fun a ha => (hD.stable τ a ha).2.1`. Simplify using `only [LieLatticeData.bc]`. Use `⟨fun a => ?_, fun b => ?_, fun a => ?_⟩` and prove the remaining obligations. Conclude with `(span_fst RC (bcMap Ω C _) (bcMap Ω C _) (D.Gam τ) (divLat w (D.W τ)) g1 a).trans (span_div RC (bcMap Ω C _) hw0 (D.W τ) a)`. Rewrite using `[← span_std RC R hR (Fin n)]`.

Conclude with `span_ker_fst RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Gam τ) (sec_fst R (D.Gam τ) sG LinearMap.id _ (locFree_div R hw0 fW) (fun v hv => (g1 v).2 hv) fun v z h => ⟨(g1 v).1 ⟨z, h⟩, rfl⟩) (stdLat R (Fin n)) g2 b`. Establish `hK` using `(LocFreeSchanuel.main R n (s τ) _ _ _ (D.Del τ) hstd (locFree_div R hw0 fH) fH sD (fun v z h => ⟨(d1 v).1 ⟨z, h⟩, (d2 z).1 ⟨v, h⟩⟩) (fun v hv => (d1 v).2 hv) d3 (fun z hz => (d2 z).2 hz)).2`. Conclude with `span_ker_snd RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Gam τ) (sec_snd R (D.Gam τ) sG _ hK fun z => (d4 z).symm) (D.W τ) g3 a`.
-/
theorem gam_bc (hD : D.Base R p w) (hw0 : w ≠ 0) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC) (τ : Sg) :
    (∀ a, (∃ b, (a, b) ∈ (D.bc RC).Gam τ) ↔ algebraMap Ω C w • a ∈ (D.bc RC).W τ) ∧
    (∀ b, (0, b) ∈ (D.bc RC).Gam τ ↔ b ∈ stdLat RC _) ∧
    ∀ a, (a, 0) ∈ (D.bc RC).Gam τ ↔ a ∈ (D.bc RC).W τ := by
  have hstd := locFree_div R hw0 (locFree_std R n)
  obtain ⟨g1, g2, g3⟩ := hD.gam τ
  obtain ⟨d1, d2, d3, d4⟩ := hD.del τ
  obtain ⟨-, fW, -, fH⟩ := hD.free τ
  have sG : ∀ a ∈ R, ∀ v ∈ D.Gam τ, a • v ∈ D.Gam τ := fun a ha => (hD.stable τ a ha).1
  have sD : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ := fun a ha => (hD.stable τ a ha).2.1
  dsimp only [LieLatticeData.bc]
  refine ⟨fun a => ?_, fun b => ?_, fun a => ?_⟩
  · exact (span_fst RC (bcMap Ω C _) (bcMap Ω C _) (D.Gam τ) (divLat w (D.W τ)) g1 a).trans
      (span_div RC (bcMap Ω C _) hw0 (D.W τ) a)
  · rw [← span_std RC R hR (Fin n)]
    exact span_ker_fst RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Gam τ)
      (sec_fst R (D.Gam τ) sG LinearMap.id _ (locFree_div R hw0 fW) (fun v hv => (g1 v).2 hv)
        fun v z h => ⟨(g1 v).1 ⟨z, h⟩, rfl⟩) (stdLat R (Fin n)) g2 b
  · have hK := (LocFreeSchanuel.main R n (s τ) _ _ _ (D.Del τ) hstd (locFree_div R hw0 fH) fH sD
      (fun v z h => ⟨(d1 v).1 ⟨z, h⟩, (d2 z).1 ⟨v, h⟩⟩) (fun v hv => (d1 v).2 hv) d3
      (fun z hz => (d2 z).2 hz)).2
    exact span_ker_snd RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Gam τ)
      (sec_snd R (D.Gam τ) sG _ hK fun z => (d4 z).symm) (D.W τ) g3 a

/- English proof (translation)
Establish `hstd` using `locFree_div R hw0 (locFree_std R n)`. Take `⟨d1, d2, d3, d4⟩` from `hD.del τ`. Take `⟨-, -, -, fH⟩` from `hD.free τ`. Establish `sD : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ` using `fun a ha => (hD.stable τ a ha).2.1`. Simplify using `only [LieLatticeData.bc]`.

Use `⟨fun b => ?_, fun y => ?_, fun y => ?_, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[← span_std RC R hR (Fin n)]`. Conclude with `(span_fst RC (bcMap Ω C _) (bcMap Ω C _) (D.Del τ) (divLat w (stdLat R (Fin n))) d1 b).trans (span_div RC (bcMap Ω C _) hw0 (stdLat R (Fin n)) b)`. Conclude with `(span_snd RC (bcMap Ω C _) (bcMap Ω C _) (D.Del τ) (divLat w (D.omHT τ)) d2 y).trans (span_div RC (bcMap Ω C _) hw0 (D.omHT τ) y)`. Conclude with `span_ker_fst RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Del τ) (sec_fst R (D.Del τ) sD LinearMap.id _ hstd (fun v hv => (d1 v).2 hv) fun v z h => ⟨(d1 v).1 ⟨z, h⟩, rfl⟩) (D.omHT τ) d3 y`.

Conclude with `(span_ker_snd RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Del τ) (sec_snd R (D.Del τ) sD _ (locFree_div R hw0 fH) d2) {z | ∃ a, (a, z) ∈ D.Gam τ} d4 b).trans (span_snd RC (bcMap Ω C _) (bcMap Ω C _) (D.Gam τ) {z | ∃ a, (a, z) ∈ D.Gam τ} (fun _ => Iff.rfl) b).symm`.
-/
theorem del_bc (hD : D.Base R p w) (hw0 : w ≠ 0) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC) (τ : Sg) :
    (∀ b, (∃ c, (b, c) ∈ (D.bc RC).Del τ) ↔ algebraMap Ω C w • b ∈ stdLat RC _) ∧
    (∀ c, (∃ b, (b, c) ∈ (D.bc RC).Del τ) ↔ algebraMap Ω C w • c ∈ (D.bc RC).omHT τ) ∧
    (∀ c, (0, c) ∈ (D.bc RC).Del τ ↔ c ∈ (D.bc RC).omHT τ) ∧
    ∀ b, (b, 0) ∈ (D.bc RC).Del τ ↔ ∃ a, (a, b) ∈ (D.bc RC).Gam τ := by
  have hstd := locFree_div R hw0 (locFree_std R n)
  obtain ⟨d1, d2, d3, d4⟩ := hD.del τ
  obtain ⟨-, -, -, fH⟩ := hD.free τ
  have sD : ∀ a ∈ R, ∀ v ∈ D.Del τ, a • v ∈ D.Del τ := fun a ha => (hD.stable τ a ha).2.1
  dsimp only [LieLatticeData.bc]
  refine ⟨fun b => ?_, fun y => ?_, fun y => ?_, fun b => ?_⟩
  · rw [← span_std RC R hR (Fin n)]
    exact (span_fst RC (bcMap Ω C _) (bcMap Ω C _) (D.Del τ) (divLat w (stdLat R (Fin n))) d1
      b).trans (span_div RC (bcMap Ω C _) hw0 (stdLat R (Fin n)) b)
  · exact (span_snd RC (bcMap Ω C _) (bcMap Ω C _) (D.Del τ) (divLat w (D.omHT τ)) d2 y).trans
      (span_div RC (bcMap Ω C _) hw0 (D.omHT τ) y)
  · exact span_ker_fst RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Del τ)
      (sec_fst R (D.Del τ) sD LinearMap.id _ hstd (fun v hv => (d1 v).2 hv)
        fun v z h => ⟨(d1 v).1 ⟨z, h⟩, rfl⟩) (D.omHT τ) d3 y
  · exact (span_ker_snd RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Del τ)
      (sec_snd R (D.Del τ) sD _ (locFree_div R hw0 fH) d2) {z | ∃ a, (a, z) ∈ D.Gam τ} d4 b).trans
      (span_snd RC (bcMap Ω C _) (bcMap Ω C _) (D.Gam τ) {z | ∃ a, (a, z) ∈ D.Gam τ}
        (fun _ => Iff.rfl) b).symm

/- English proof (translation)
Establish `hpC : algebraMap Ω C (p : Ω) = (p : C)` using `map_natCast _ p`. Establish `haug : ∀ g ∈ D.M, aug Ω (0 : Fin n → F) g ∈ D.M` using `fun g hg => D.M.sub_mem hg (hD.freeM.1 _ ((mem_std R _).1 (hD.M_le hg) 0) _ hD.one_mem)`. Take `⟨t1, t2, t3⟩` from `hD.th τ`. Establish `sT : ∀ a ∈ R, ∀ v ∈ D.Th τ, a • v ∈ D.Th τ` using `fun a ha => (hD.stable τ a ha).2.2`. Simplify using `only [LieLatticeData.bc]`.

Establish `hdual` using `(PositivityTheory.Xgn.t_dotdual_bc R RC hR _ _ (hD.free τ).1).2.2`. Rewrite using `[hdual]`. Use `⟨fun g => ?_, fun m => ?_, fun m => ?_⟩` and prove the remaining obligations. Conclude with `(span_fst RC (bcMap Ω C _) (bcMap Ω C _) (D.Th τ) {g | g ∈ D.M ∧ g 0 = 0} t1 g).trans (span_aug RC 0 D.M haug g)`. Conclude with `span_snd RC (bcMap Ω C _) (bcMap Ω C _) (D.Th τ) (dotDual R (D.lie τ)) t2 m`.

Rewrite using `[← hpC, ← span_mul]`. Use `span_ker_fst RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Th τ) (sec_fst R (D.Th τ) sT (aug Ω 0) _ hD.freeM (fun v hv => (t1 _).2 ⟨haug v hv, by simp [aug_apply]⟩) fun v z h => ?_) (mulLat (p : Ω) (dotDual R (D.lie τ))) t3 m` and prove the remaining obligations. Take `⟨h1, h2⟩` from `(t1 v).1 ⟨z, h⟩`. Conclude with `⟨h1, by simp [aug_apply, h2]⟩`.
-/
theorem th_bc [IsScalarTower o Ω C] (hD : D.Base R p w) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    (τ : Sg) :
    (∀ g, (∃ m, (g, m) ∈ (D.bc RC).Th τ) ↔ g ∈ (D.bc RC).M ∧ g 0 = 0) ∧
    (∀ m, (∃ g, (g, m) ∈ (D.bc RC).Th τ) ↔ m ∈ dotDual RC ((D.bc RC).lie τ)) ∧
    ∀ m, (0, m) ∈ (D.bc RC).Th τ ↔ m ∈ mulLat (p : C) (dotDual RC ((D.bc RC).lie τ)) := by
  have hpC : algebraMap Ω C (p : Ω) = (p : C) := map_natCast _ p
  have haug : ∀ g ∈ D.M, aug Ω (0 : Fin n → F) g ∈ D.M := fun g hg =>
    D.M.sub_mem hg (hD.freeM.1 _ ((mem_std R _).1 (hD.M_le hg) 0) _ hD.one_mem)
  obtain ⟨t1, t2, t3⟩ := hD.th τ
  have sT : ∀ a ∈ R, ∀ v ∈ D.Th τ, a • v ∈ D.Th τ := fun a ha => (hD.stable τ a ha).2.2
  dsimp only [LieLatticeData.bc]
  have hdual :=
    (PositivityTheory.Xgn.t_dotdual_bc R RC hR _ _ (hD.free τ).1).2.2
  rw [hdual]
  refine ⟨fun g => ?_, fun m => ?_, fun m => ?_⟩
  · exact (span_fst RC (bcMap Ω C _) (bcMap Ω C _) (D.Th τ) {g | g ∈ D.M ∧ g 0 = 0} t1 g).trans
      (span_aug RC 0 D.M haug g)
  · exact span_snd RC (bcMap Ω C _) (bcMap Ω C _) (D.Th τ) (dotDual R (D.lie τ)) t2 m
  · rw [← hpC, ← span_mul]
    refine span_ker_fst RC (bcMap Ω C _) (bcMap Ω C _) (isBC Ω C _) (D.Th τ)
      (sec_fst R (D.Th τ) sT (aug Ω 0) _ hD.freeM
        (fun v hv => (t1 _).2 ⟨haug v hv, by simp [aug_apply]⟩) fun v z h => ?_)
      (mulLat (p : Ω) (dotDual R (D.lie τ))) t3 m
    obtain ⟨h1, h2⟩ := (t1 v).1 ⟨z, h⟩
    exact ⟨h1, by simp [aug_apply, h2]⟩

end Clauses

end PositivityTheory.Xgn.LocallyFreeLatticeSpans

open PositivityTheory.Xgn.A_graph_restrict_bc PositivityTheory.Xgn.LocallyFreeLatticeSpans in
/- English proof (translation)
Introduce `o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hD C _ _ _ _ RC hR`. Take `⟨hp, hw, ⟨c, hc, hpc⟩, h01, hχ⟩` from `hχ`. Establish `hw0 : w ≠ 0`. Introduce and unpack `rfl`. Conclude with `hp (by simpa using hpc)`.

Establish `hpC : algebraMap Ω C (p : Ω) = (p : C)` using `map_natCast _ p`. Establish `fr` using `fun (ι : Type) [Finite ι] (N : ℕ) (L : AddSubgroup (ι → Ω)) (h : LocFree R N L) => LocFreeBC.locFree_baseChange R RC hR (bcMap Ω C ι) (isBC Ω C ι) N L h`. Use `⟨⟨?_, hR w hw, ⟨_, hR c hc, ?_⟩, h01, fun τ => ⟨?_, ?_, fun a => hR _ ((hχ τ).2.2 a)⟩⟩, ⟨fr _ _ _ hD.freeM, ?_, ?_, ?_, fun τ => ?_, fun τ => ?_, fun τ a ha => ?_, gam_bc hD hw0 hR, del_bc hD hw0 hR, th_bc hD hR⟩⟩` and prove the remaining obligations. Rewrite using `[← hpC]`. Simplify `hp` using `only [ne_eq, map_eq_zero]`.

Rewrite using `[← hpC, hpc, map_mul]`. Simplify using `[(hχ τ).1]`. Simplify using `[(hχ τ).2.1]`. Rewrite using `[← span_std RC R hR]`. Conclude with `span_mono RC _ hD.M_le`.

Take `⟨m, hm⟩` from `hD.le_M`. Use `⟨m, fun x hx => span_mono RC _ hm ?_⟩` and prove the remaining obligations. Rewrite using `[span_mul, span_std RC R hR, map_pow, hpC]`. Conclude with `hx`. Use `mem_span ⟨1, hD.one_mem, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Simplify using `[bcMap]`. Take `⟨h1, h2, h3, h4⟩` from `hD.free τ`. Conclude with `⟨fr _ _ _ h1, fr _ _ _ h2, fr _ _ _ h3, fr _ _ _ h4⟩`. Take `⟨h1, h2, h3, h4⟩` from `hD.incl τ`.

Conclude with `⟨span_mono RC _ h1, fun x hx => (span_div RC _ hw0 _ x).1 (span_mono RC _ h2 hx), span_mono RC _ h3, fun x hx => (span_div RC _ hw0 _ x).1 (span_mono RC _ h4 hx)⟩`. Conclude with `⟨fun v hv => smul_mem ha hv, fun v hv => smul_mem ha hv, fun v hv => smul_mem ha hv⟩`.
-/
theorem PositivityTheory.Xgn.character_data_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → CharData RC p (algebraMap Ω C w) (fun τ a => algebraMap Ω C (χ τ a)) ∧ (D.bc RC).Base RC p (algebraMap Ω C w) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hχ hD C _ _ _ _ RC hR
  obtain ⟨hp, hw, ⟨c, hc, hpc⟩, h01, hχ⟩ := hχ
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hp (by simpa using hpc)
  have hpC : algebraMap Ω C (p : Ω) = (p : C) := map_natCast _ p
  have fr := fun (ι : Type) [Finite ι] (N : ℕ) (L : AddSubgroup (ι → Ω)) (h : LocFree R N L) =>
    LocFreeBC.locFree_baseChange R RC hR (bcMap Ω C ι) (isBC Ω C ι) N L h
  refine ⟨⟨?_, hR w hw, ⟨_, hR c hc, ?_⟩, h01, fun τ => ⟨?_, ?_, fun a => hR _ ((hχ τ).2.2 a)⟩⟩,
    ⟨fr _ _ _ hD.freeM, ?_, ?_, ?_, fun τ => ?_, fun τ => ?_, fun τ a ha => ?_, gam_bc hD hw0 hR,
      del_bc hD hw0 hR, th_bc hD hR⟩⟩
  · rw [← hpC]
    simpa only [ne_eq, map_eq_zero] using hp
  · rw [← hpC, hpc, map_mul]
  · simp [(hχ τ).1]
  · simp [(hχ τ).2.1]
  · rw [← span_std RC R hR]
    exact span_mono RC _ hD.M_le
  · obtain ⟨m, hm⟩ := hD.le_M
    refine ⟨m, fun x hx => span_mono RC _ hm ?_⟩
    rw [span_mul, span_std RC R hR, map_pow, hpC]
    exact hx
  · refine mem_span ⟨1, hD.one_mem, ?_⟩
    funext j
    simp [bcMap]
  · obtain ⟨h1, h2, h3, h4⟩ := hD.free τ
    exact ⟨fr _ _ _ h1, fr _ _ _ h2, fr _ _ _ h3, fr _ _ _ h4⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hD.incl τ
    exact ⟨span_mono RC _ h1, fun x hx => (span_div RC _ hw0 _ x).1 (span_mono RC _ h2 hx),
      span_mono RC _ h3, fun x hx => (span_div RC _ hw0 _ x).1 (span_mono RC _ h4 hx)⟩
  · exact ⟨fun v hv => smul_mem ha hv, fun v hv => smul_mem ha hv, fun v hv => smul_mem ha hv⟩
