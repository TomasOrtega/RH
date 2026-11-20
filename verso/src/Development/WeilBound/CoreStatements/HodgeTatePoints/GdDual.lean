import Development.WeilBound.CoreStatements.HodgeTatePoints.TorusExtensionPairCorrectionEqValueQuotient
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

noncomputable section

namespace PositivityTheory.HtPt.Gd

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [IsAlgClosed C] [CharZero C]
  {E : Type} [Field E] [NumberField E] {c : E ≃+* E} {κ : O} {N : ℕ}
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  {Ω : Type} [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]

omit [IsAlgClosed C] [CharZero C] in

/- English proof (translation)
Conclude with `⟨P.ht y, ⟨y, hy, rfl⟩, rfl⟩`.
-/
theorem proj_ht_mem (P : HTPoint C O c κ N V Ω) (τ : E →+* C) {y : V} (hy : y ∈ P.T) :
    eigProj P.ρΩ τ (P.ht y) ∈ P.omHT τ := by
  exact ⟨P.ht y, ⟨y, hy, rfl⟩, rfl⟩

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Establish `h` using `P.alt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h`. Take the linear combination `h`.
-/
private theorem htPoint_e_antisymm (P : HTPoint C O c κ N V Ω) (x y : V) : P.e x y = - P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  linear_combination h

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
The claim follows from `P.nondeg x (fun z => by rw [htPoint_e_antisymm P z x, h z, neg_zero])`.
-/
private theorem htPoint_eq_zero_of_e_left_eq_zero (P : HTPoint C O c κ N V Ω) {x : V} (h : ∀ y, P.e x y = 0) : x = 0 :=
  P.nondeg x (fun z => by rw [htPoint_e_antisymm P z x, h z, neg_zero])

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Establish `hfree : IsFreeOn P.ρ P.T P.t` using `P.free`. Take `⟨hli, hspan, hT⟩` from `hfree`. Establish `hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => P.ρ (RingOfIntegers.basis E q.2) (P.t q.1))`. Rewrite using `[← hspan]`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises.

Introduce `y hy`. Rewrite `hy` using `[hT]`. Conclude with `Submodule.span_subset_span O C _ hy`. Conclude with `⟨Basis.mk hli hsp, fun q => Basis.mk_apply hli hsp q, hT⟩`.
-/
private theorem htPoint_exists_basis_rho_t_span (P : HTPoint C O c κ N V Ω) :
    ∃ B : Basis (Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E)) C V,
      (∀ q, B q = P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∧
      P.T = Submodule.span O (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := by
  have hfree : IsFreeOn P.ρ P.T P.t := P.free
  obtain ⟨hli, hspan, hT⟩ := hfree
  have hsp : ⊤ ≤ Submodule.span C (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    intro y hy
    rw [hT] at hy
    exact Submodule.span_subset_span O C _ hy
  exact ⟨Basis.mk hli hsp, fun q => Basis.mk_apply hli hsp q, hT⟩

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Take `⟨B, hB, hT⟩` from `htPoint_exists_basis_rho_t_span P`. Establish `hbT : ∀ q, B q ∈ P.T`. Introduce `q`. Rewrite using `[hB, hT]`. Conclude with `Submodule.subset_span ⟨q, rfl⟩`.

Use `⟨B.constr C (fun q => algebraMap O C (g ⟨B q, hbT q⟩)), ?_⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : y ∈ Submodule.span O (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => P.ρ (RingOfIntegers.basis E q.2) (P.t q.1))` using `hT ▸ hy`. Use `revert hy`. Proceed by induction on `hy' using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨q, rfl⟩` from `hx`. Introduce `hy`. Establish `e2 : (⟨_, hy⟩ : P.T) = ⟨B q, hbT q⟩` using `Subtype.ext (hB q).symm`. Rewrite using `[e2]`.

Establish `h1` using `B.constr_basis C (fun q => algebraMap O C (g ⟨B q, hbT q⟩)) q`. Conclude with `(congrArg (B.constr C (fun q => algebraMap O C (g ⟨B q, hbT q⟩))) (hB q)).symm.trans h1`. Consider the case `zero`. Introduce `hy`. Establish `: (⟨0, hy⟩ : P.T) = 0` using `rfl`.

Rewrite using `[map_zero, this, map_zero, map_zero]`. Consider the case `add x z hx hz ihx ihz`. Introduce `hy`. Establish `hxT : x ∈ P.T` using `hT ▸ hx`. Establish `hzT : z ∈ P.T` using `hT ▸ hz`.

Establish `: (⟨x + z, hy⟩ : P.T) = ⟨x, hxT⟩ + ⟨z, hzT⟩` using `rfl`. Rewrite using `[map_add, this, map_add, map_add, ihx hxT, ihz hzT]`. Consider the case `smul a x hx ihx`. Introduce `hy`. Establish `hxT : x ∈ P.T` using `hT ▸ hx`.

Establish `: (⟨a • x, hy⟩ : P.T) = a • ⟨x, hxT⟩` using `rfl`. Rewrite using `[this, ← algebraMap_smul C a x, LinearMap.map_smul, LinearMap.map_smul, ihx hxT, smul_eq_mul, smul_eq_mul, map_mul]`.
-/
private theorem htPoint_exists_linearMap_ext_of_T (P : HTPoint C O c κ N V Ω) (g : P.T →ₗ[O] O) :
    ∃ ℓ : V →ₗ[C] C, ∀ y (hy : y ∈ P.T), ℓ y = algebraMap O C (g ⟨y, hy⟩) := by
  obtain ⟨B, hB, hT⟩ := htPoint_exists_basis_rho_t_span P
  have hbT : ∀ q, B q ∈ P.T := by
    intro q
    rw [hB, hT]
    exact Submodule.subset_span ⟨q, rfl⟩
  refine ⟨B.constr C (fun q => algebraMap O C (g ⟨B q, hbT q⟩)), ?_⟩
  intro y hy
  have hy' : y ∈ Submodule.span O (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) := hT ▸ hy
  revert hy
  induction hy' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    intro hy
    have e2 : (⟨_, hy⟩ : P.T) = ⟨B q, hbT q⟩ := Subtype.ext (hB q).symm
    rw [e2]
    have h1 := B.constr_basis C (fun q => algebraMap O C (g ⟨B q, hbT q⟩)) q
    exact (congrArg (B.constr C (fun q => algebraMap O C (g ⟨B q, hbT q⟩))) (hB q)).symm.trans h1
  | zero =>
    intro hy
    have : (⟨0, hy⟩ : P.T) = 0 := rfl
    rw [map_zero, this, map_zero, map_zero]
  | add x z hx hz ihx ihz =>
    intro hy
    have hxT : x ∈ P.T := hT ▸ hx
    have hzT : z ∈ P.T := hT ▸ hz
    have : (⟨x + z, hy⟩ : P.T) = ⟨x, hxT⟩ + ⟨z, hzT⟩ := rfl
    rw [map_add, this, map_add, map_add, ihx hxT, ihz hzT]
  | smul a x hx ihx =>
    intro hy
    have hxT : x ∈ P.T := hT ▸ hx
    have : (⟨a • x, hy⟩ : P.T) = a • ⟨x, hxT⟩ := rfl
    rw [this, ← algebraMap_smul C a x, LinearMap.map_smul, LinearMap.map_smul, ihx hxT,
      smul_eq_mul, smul_eq_mul, map_mul]

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Take `⟨B, -, -⟩` from `htPoint_exists_basis_rho_t_span P`. Use `haveI : FiniteDimensional C V := Module.Finite.of_basis B`. Establish `hinj : Function.Injective P.e`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`.

Conclude with `htPoint_eq_zero_of_e_left_eq_zero P (fun y => by rw [hx, LinearMap.zero_apply])`. Establish `hsurj : Function.Surjective P.e` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hinj`. Take `⟨w, hw⟩` from `hsurj ℓ`. Conclude with `⟨w, fun y => by rw [hw]⟩`.
-/
private theorem htPoint_exists_e_left_eq_linearMap (P : HTPoint C O c κ N V Ω) (ℓ : V →ₗ[C] C) :
    ∃ w : V, ∀ y, P.e w y = ℓ y := by
  obtain ⟨B, -, -⟩ := htPoint_exists_basis_rho_t_span P
  haveI : FiniteDimensional C V := Module.Finite.of_basis B
  have hinj : Function.Injective P.e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact htPoint_eq_zero_of_e_left_eq_zero P (fun y => by rw [hx, LinearMap.zero_apply])
  have hsurj : Function.Surjective P.e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).mp hinj
  obtain ⟨w, hw⟩ := hsurj ℓ
  exact ⟨w, fun y => by rw [hw]⟩

omit [IsAlgClosed C] [CharZero C] in

/- English proof (translation)
Take `⟨ℓ, hℓ⟩` from `htPoint_exists_linearMap_ext_of_T P g`. Take `⟨w, hw⟩` from `htPoint_exists_e_left_eq_linearMap P ℓ`. Conclude with `⟨w, fun y => by rw [hw]; exact hℓ y y.2⟩`.
-/
theorem exists_vec (P : HTPoint C O c κ N V Ω) (g : P.T →ₗ[O] O) :
    ∃ w : V, ∀ y : P.T, P.e w y = algebraMap O C (g y) := by
  obtain ⟨ℓ, hℓ⟩ := htPoint_exists_linearMap_ext_of_T P g
  obtain ⟨w, hw⟩ := htPoint_exists_e_left_eq_linearMap P ℓ
  exact ⟨w, fun y => by rw [hw]; exact hℓ y y.2⟩

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Establish `hsc : ∀ a : C, ∃ s : O, algebraMap O C s ≠ 0 ∧ ∃ u : O, algebraMap O C u = algebraMap O C s * a`. Introduce `a`. Distinguish the cases in `ha : v a ≤ 1`. Take `⟨u, hu⟩` from `hv.exists_of_le_one ha`. Conclude with `⟨1, by simp, u, by simp [hu]⟩`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at ha`. Establish `hle : v a⁻¹ ≤ 1`. Rewrite using `[map_inv₀]`.

Use `push_neg at ha`. Conclude with `inv_le_one_of_one_le₀ ha.le`. Take `⟨s, hs⟩` from `hv.exists_of_le_one hle`. Conclude with `⟨s, by rw [hs]; exact inv_ne_zero ha0, 1, by rw [hs, map_one, inv_mul_cancel₀ ha0]⟩`. Establish `hfree : IsFreeOn P.ρ P.T P.t` using `P.free`.

Take `⟨-, hspan, -⟩` from `hfree`. Establish `hy : y ∈ Submodule.span C (P.T : Set V)` using `hspan ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, by simp, by rw [one_smul]; exact hx⟩`. Consider the case `zero => exact ⟨1, by simp, by rw [smul_zero]; exact P.T.zero_mem⟩`.

Consider the case `add x z _ _ ihx ihz`. Take `⟨s, hs, hsx⟩` from `ihx`. Take `⟨r, hr, hrz⟩` from `ihz`. Use `⟨s * r, by rw [map_mul]; exact mul_ne_zero hs hr, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, mul_smul s r z, mul_comm s r, mul_smul r s x]`.

Conclude with `P.T.add_mem (P.T.smul_mem r hsx) (P.T.smul_mem s hrz)`. Consider the case `smul a x _ ihx`. Take `⟨s, hs, hsx⟩` from `ihx`. Take `⟨t, ht, u, hu⟩` from `hsc a`. Use `⟨t * s, by rw [map_mul]; exact mul_ne_zero ht hs, ?_⟩` and prove the remaining obligations.

Establish `key : (t * s) • (a • x) = u • (s • x)`. Rewrite using `[← algebraMap_smul C (t * s), ← algebraMap_smul C u, ← algebraMap_smul C s, smul_smul, smul_smul, map_mul, hu]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `P.T.smul_mem u hsx`.
-/
private theorem htPoint_exists_smul_mem_T (hv : v.Integers O) (P : HTPoint C O c κ N V Ω) (y : V) :
    ∃ s : O, algebraMap O C s ≠ 0 ∧ s • y ∈ P.T := by
  have hsc : ∀ a : C, ∃ s : O, algebraMap O C s ≠ 0 ∧ ∃ u : O, algebraMap O C u = algebraMap O C s * a := by
    intro a
    by_cases ha : v a ≤ 1
    · obtain ⟨u, hu⟩ := hv.exists_of_le_one ha
      exact ⟨1, by simp, u, by simp [hu]⟩
    · have ha0 : a ≠ 0 := by
        rintro rfl
        simp at ha
      have hle : v a⁻¹ ≤ 1 := by
        rw [map_inv₀]
        push_neg at ha
        exact inv_le_one_of_one_le₀ ha.le
      obtain ⟨s, hs⟩ := hv.exists_of_le_one hle
      exact ⟨s, by rw [hs]; exact inv_ne_zero ha0, 1, by rw [hs, map_one, inv_mul_cancel₀ ha0]⟩
  have hfree : IsFreeOn P.ρ P.T P.t := P.free
  obtain ⟨-, hspan, -⟩ := hfree
  have hy : y ∈ Submodule.span C (P.T : Set V) := hspan ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simp, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, by simp, by rw [smul_zero]; exact P.T.zero_mem⟩
  | add x z _ _ ihx ihz =>
    obtain ⟨s, hs, hsx⟩ := ihx
    obtain ⟨r, hr, hrz⟩ := ihz
    refine ⟨s * r, by rw [map_mul]; exact mul_ne_zero hs hr, ?_⟩
    rw [smul_add, mul_smul s r z, mul_comm s r, mul_smul r s x]
    exact P.T.add_mem (P.T.smul_mem r hsx) (P.T.smul_mem s hrz)
  | smul a x _ ihx =>
    obtain ⟨s, hs, hsx⟩ := ihx
    obtain ⟨t, ht, u, hu⟩ := hsc a
    refine ⟨t * s, by rw [map_mul]; exact mul_ne_zero ht hs, ?_⟩
    have key : (t * s) • (a • x) = u • (s • x) := by
      rw [← algebraMap_smul C (t * s), ← algebraMap_smul C u, ← algebraMap_smul C s, smul_smul,
        smul_smul, map_mul, hu]
      congr 1
      ring
    rw [key]
    exact P.T.smul_mem u hsx

omit [IsAlgClosed C] [CharZero C] in
/- English proof (translation)
Take `⟨B, -, hT⟩` from `htPoint_exists_basis_rho_t_span P`. Rewrite `hz`, the goal using `[hT]`. Use `set S := Submodule.span O (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) with hS`. Establish `key : ∀ (m : 𝓞 E) (i : Fin N), P.ρ m (P.t i) ∈ S`. Introduce `m i`.

Establish `hm : m ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E))`. Rewrite using `[(RingOfIntegers.basis E).span_eq]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨j, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨(i, j), rfl⟩`. Consider the case `zero`. Rewrite using `[map_zero, LinearMap.zero_apply]`. Conclude with `S.zero_mem`.

Consider the case `add x z _ _ hx hz`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `S.add_mem hx hz`. Consider the case `smul n x _ hx`. Simplify using `only [map_zsmul, LinearMap.smul_apply]`.

Conclude with `zsmul_mem hx n`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨q, rfl⟩` from `hx`. Use `show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ S`.

Rewrite using `[← Module.End.mul_apply, ← map_mul]`. Conclude with `key _ _`. Consider the case `zero`. Rewrite using `[map_zero]`. Conclude with `S.zero_mem`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `S.add_mem hx hy`. Consider the case `smul o x _ hx`. Rewrite using `[LinearMap.map_smul_of_tower]`.

Conclude with `S.smul_mem o hx`.
-/
private theorem htPoint_rho_mem_T (P : HTPoint C O c κ N V Ω) (a : 𝓞 E) {z : V} (hz : z ∈ P.T) :
    P.ρ a z ∈ P.T := by
  obtain ⟨B, -, hT⟩ := htPoint_exists_basis_rho_t_span P
  rw [hT] at hz ⊢
  set S := Submodule.span O (Set.range fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
    P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) with hS
  have key : ∀ (m : 𝓞 E) (i : Fin N), P.ρ m (P.t i) ∈ S := by
    intro m i
    have hm : m ∈ Submodule.span ℤ (Set.range (RingOfIntegers.basis E)) := by
      rw [(RingOfIntegers.basis E).span_eq]
      exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨(i, j), rfl⟩
    | zero =>
      rw [map_zero, LinearMap.zero_apply]
      exact S.zero_mem
    | add x z _ _ hx hz =>
      rw [map_add, LinearMap.add_apply]
      exact S.add_mem hx hz
    | smul n x _ hx =>
      simp only [map_zsmul, LinearMap.smul_apply]
      exact zsmul_mem hx n
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ S
    rw [← Module.End.mul_apply, ← map_mul]
    exact key _ _
  | zero =>
    rw [map_zero]
    exact S.zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact S.add_mem hx hy
  | smul o x _ hx =>
    rw [LinearMap.map_smul_of_tower]
    exact S.smul_mem o hx

/- English proof (translation)
Set `K : P.T →ₗ[O] P.omHT (σ.comp c.toRingHom)` to `LinearMap.codRestrict (P.omHT (σ.comp c.toRingHom)) (((eigProj P.ρΩ (σ.comp c.toRingHom)).restrictScalars O).comp ((P.ht.restrictScalars O).comp P.T.subtype)) (fun y => proj_ht_mem P (σ.comp c.toRingHom) y.2)`. Take `⟨ℓ, hℓ⟩` from `htPoint_exists_linearMap_ext_of_T P (f.comp K)`. Take `⟨w, hw⟩` from `htPoint_exists_e_left_eq_linearMap P ℓ`. Establish `hK : ∀ y (hy : y ∈ P.T), (K ⟨y, hy⟩ : Ω) = eigProj P.ρΩ (σ.comp c.toRingHom) (P.ht y)` using `fun y hy => rfl`. Establish `hℓs : ∀ (s : O) (y : V), ℓ (s • y) = algebraMap O C s * ℓ y`.

Introduce `s y`. Rewrite using `[← algebraMap_smul C s y, LinearMap.map_smul, smul_eq_mul]`. Establish `hker : P.ht w = 0`. Rewrite using `[P.lagr w]`. Introduce `y hy0`.

Rewrite using `[hw]`. Take `⟨s, hs, hsy⟩` from `htPoint_exists_smul_mem_T hv P y`. Establish `h0 : K ⟨s • y, hsy⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [hK, LinearMap.map_smul_of_tower, hy0, smul_zero, map_zero, Submodule.coe_zero]`.

Establish `h1` using `hℓ (s • y) hsy`. Rewrite `h1` using `[LinearMap.comp_apply, h0, map_zero, map_zero, hℓs]`. Conclude with `(mul_eq_zero.mp h1).resolve_left hs`. Establish `hσu : ∀ a : 𝓞 E, ∃ u : O, algebraMap O C u = σ (a : E)`. Introduce `a`.

Establish `hint : IsIntegral O (σ (a : E))`. Establish `h` using `(NumberField.RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom`. Conclude with `h.tower_top`. Conclude with `hv.exists_of_le_one (hv.mem_of_integral hint)`. Establish `hρ : ∀ (a : 𝓞 E) (y : V), ℓ (P.ρ (RingOfIntegers.mapRingEquiv c a) y) = σ (a : E) * ℓ y`.

Introduce `a y`. Take `⟨u, hu⟩` from `hσu a`. Establish `hT1 : ∀ z (hz : z ∈ P.T), ℓ (P.ρ (RingOfIntegers.mapRingEquiv c a) z) = σ (a : E) * ℓ z`. Introduce `z hz`. Establish `hz'` using `htPoint_rho_mem_T P (RingOfIntegers.mapRingEquiv c a) hz`.

Establish `hK2 : K ⟨_, hz'⟩ = u • K ⟨z, hz⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e3` using `LinearMap.congr_fun ((ProjEig.eigProj_mul_rho_comm P.ρΩ (σ.comp c.toRingHom) (RingOfIntegers.mapRingEquiv c a)).trans (ProjEig.rho_mul_eigProj P.ρΩ (σ.comp c.toRingHom) (RingOfIntegers.mapRingEquiv c a))) (P.ht z)`. Rewrite `e3` using `[Module.End.mul_apply, LinearMap.smul_apply]`. Establish `e4 : (σ.comp c.toRingHom) ((RingOfIntegers.mapRingEquiv c a : 𝓞 E) : E) = algebraMap O C u`.

Rewrite using `[hu]`. Simplify using `[hc]`. Rewrite using `[Submodule.coe_smul, hK, hK, P.ht_lin, e3, e4, algebraMap_smul]`. Rewrite using `[hℓ _ hz', hℓ z hz, LinearMap.comp_apply, LinearMap.comp_apply, hK2, map_smul, smul_eq_mul, map_mul, hu]`. Take `⟨s, hs, hsy⟩` from `htPoint_exists_smul_mem_T hv P y`.

Establish `h1` using `hT1 _ hsy`. Rewrite `h1` using `[LinearMap.map_smul_of_tower, hℓs, hℓs]`. Apply `mul_left_cancel₀ hs` to reduce the goal to its premises. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.

Establish `heig : ∀ a : 𝓞 E, P.ρ a w = σ (a : E) • w`. Introduce `a`. Establish `h0 : P.ρ a w - σ (a : E) • w = 0`. Apply `htPoint_eq_zero_of_e_left_eq_zero P` to reduce the goal to its premises. Introduce `y`.

Rewrite using `[map_sub, LinearMap.sub_apply, P.adj, map_smul, LinearMap.smul_apply, hw, hw, smul_eq_mul, hρ, sub_self]`. Conclude with `sub_eq_zero.mp h0`. Use `⟨w, Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem]`. Conclude with `LinearMap.mem_ker.mpr hker`.

Rewrite using `[← P.perfect]`. Introduce `x hx`. Rewrite using `[htPoint_e_antisymm P x w, hw, hℓ x hx]`. Conclude with `RingHom.mem_range.mpr ⟨_, map_neg _ _⟩`. Rewrite using `[Submodule.restrictScalars_mem]`.

Simplify using `only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `a`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, heig, sub_self]`. Rewrite using `[hw]`. Conclude with `hℓ y hy`.
-/
theorem exists_alt_bis (hv : v.Integers O) (hc : ∀ x, c (c x) = x) (P : HTPoint C O c κ N V Ω) (σ : E →+* C)
    (f : P.omHT (σ.comp c.toRingHom) →ₗ[O] O) :
    ∃ w ∈ P.W' σ, ∀ y (hy : y ∈ P.T),
      P.e w y = algebraMap O C (f ⟨_, proj_ht_mem P (σ.comp c.toRingHom) hy⟩) := by
  let K : P.T →ₗ[O] P.omHT (σ.comp c.toRingHom) :=
    LinearMap.codRestrict (P.omHT (σ.comp c.toRingHom))
      (((eigProj P.ρΩ (σ.comp c.toRingHom)).restrictScalars O).comp
        ((P.ht.restrictScalars O).comp P.T.subtype))
      (fun y => proj_ht_mem P (σ.comp c.toRingHom) y.2)
  obtain ⟨ℓ, hℓ⟩ := htPoint_exists_linearMap_ext_of_T P (f.comp K)
  obtain ⟨w, hw⟩ := htPoint_exists_e_left_eq_linearMap P ℓ
  have hK : ∀ y (hy : y ∈ P.T), (K ⟨y, hy⟩ : Ω) = eigProj P.ρΩ (σ.comp c.toRingHom) (P.ht y) :=
    fun y hy => rfl
  have hℓs : ∀ (s : O) (y : V), ℓ (s • y) = algebraMap O C s * ℓ y := by
    intro s y
    rw [← algebraMap_smul C s y, LinearMap.map_smul, smul_eq_mul]
  have hker : P.ht w = 0 := by
    rw [P.lagr w]
    intro y hy0
    rw [hw]
    obtain ⟨s, hs, hsy⟩ := htPoint_exists_smul_mem_T hv P y
    have h0 : K ⟨s • y, hsy⟩ = 0 := by
      apply Subtype.ext
      simp only [hK, LinearMap.map_smul_of_tower, hy0, smul_zero, map_zero, Submodule.coe_zero]
    have h1 := hℓ (s • y) hsy
    rw [LinearMap.comp_apply, h0, map_zero, map_zero, hℓs] at h1
    exact (mul_eq_zero.mp h1).resolve_left hs
  have hσu : ∀ a : 𝓞 E, ∃ u : O, algebraMap O C u = σ (a : E) := by
    intro a
    have hint : IsIntegral O (σ (a : E)) := by
      have h := (NumberField.RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
      exact h.tower_top
    exact hv.exists_of_le_one (hv.mem_of_integral hint)
  have hρ : ∀ (a : 𝓞 E) (y : V),
      ℓ (P.ρ (RingOfIntegers.mapRingEquiv c a) y) = σ (a : E) * ℓ y := by
    intro a y
    obtain ⟨u, hu⟩ := hσu a
    have hT1 : ∀ z (hz : z ∈ P.T),
        ℓ (P.ρ (RingOfIntegers.mapRingEquiv c a) z) = σ (a : E) * ℓ z := by
      intro z hz
      have hz' := htPoint_rho_mem_T P (RingOfIntegers.mapRingEquiv c a) hz
      have hK2 : K ⟨_, hz'⟩ = u • K ⟨z, hz⟩ := by
        apply Subtype.ext
        have e3 := LinearMap.congr_fun
          ((ProjEig.eigProj_mul_rho_comm P.ρΩ (σ.comp c.toRingHom) (RingOfIntegers.mapRingEquiv c a)).trans
            (ProjEig.rho_mul_eigProj P.ρΩ (σ.comp c.toRingHom) (RingOfIntegers.mapRingEquiv c a))) (P.ht z)
        rw [Module.End.mul_apply, LinearMap.smul_apply] at e3
        have e4 : (σ.comp c.toRingHom) ((RingOfIntegers.mapRingEquiv c a : 𝓞 E) : E) = algebraMap O C u := by
          rw [hu]
          simp [hc]
        rw [Submodule.coe_smul, hK, hK, P.ht_lin, e3, e4, algebraMap_smul]
      rw [hℓ _ hz', hℓ z hz, LinearMap.comp_apply, LinearMap.comp_apply, hK2, map_smul, smul_eq_mul,
        map_mul, hu]
    obtain ⟨s, hs, hsy⟩ := htPoint_exists_smul_mem_T hv P y
    have h1 := hT1 _ hsy
    rw [LinearMap.map_smul_of_tower, hℓs, hℓs] at h1
    apply mul_left_cancel₀ hs
    rw [h1]
    ring
  have heig : ∀ a : 𝓞 E, P.ρ a w = σ (a : E) • w := by
    intro a
    have h0 : P.ρ a w - σ (a : E) • w = 0 := by
      apply htPoint_eq_zero_of_e_left_eq_zero P
      intro y
      rw [map_sub, LinearMap.sub_apply, P.adj, map_smul, LinearMap.smul_apply, hw, hw, smul_eq_mul,
        hρ, sub_self]
    exact sub_eq_zero.mp h0
  refine ⟨w, Submodule.mem_inf.mpr ⟨?_, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩, fun y hy => ?_⟩
  · rw [Submodule.restrictScalars_mem]
    exact LinearMap.mem_ker.mpr hker
  · rw [← P.perfect]
    intro x hx
    rw [htPoint_e_antisymm P x w, hw, hℓ x hx]
    exact RingHom.mem_range.mpr ⟨_, map_neg _ _⟩
  · rw [Submodule.restrictScalars_mem]
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, heig, sub_self]
  · rw [hw]
    exact hℓ y hy

end PositivityTheory.HtPt.Gd
