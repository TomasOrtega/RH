import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.MuRange

open Polynomial TensorProduct UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Z.Desc.V0

namespace UpperTheory.V.Z.Desc.V0.GeneralizedEigenRange

section Lin

variable {K V V' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']

end Lin

section Mu

variable {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B]
  (lam : Λ →ₐ[O] B) {M M' : Type} [AddCommGroup M] [Module B M] [Module Λ M]
  [AddCommGroup M'] [Module B M'] [Module Λ M']
  (hs : ∀ (a : Λ) (m : M), a • m = lam a • m) (hs' : ∀ (a : Λ) (m : M'), a • m = lam a • m)

end Mu

end UpperTheory.V.Z.Desc.V0.GeneralizedEigenRange

open UpperTheory.V.Z.Desc.V0.GeneralizedEigenRange

/- English proof (translation)
Unfold `MuRange`. Introduce `O L B K _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he`. Use `letI : Algebra L B := (lam : L →+* B).toAlgebra`. Use `haveI : IsScalarTower L B M := ⟨fun a b m => by`. Rewrite using `[Algebra.smul_def, mul_smul, h.hs]`.

Use the proof step `rfl⟩`. Set `eB : M →ₗ[B] M` to `{ toFun := e, map_add' := e.map_add, map_smul' := fun b m => he.2 b m }`. Set `P : Submodule B M` to `LinearMap.range eB`. Establish `hsP : ∀ (a : L) (m : P), a • m = lam a • m` using `fun a m => Subtype.ext (h.hs a m.1)`. Establish `hee : ∀ m, e (e m) = e m` using `fun m => by`.

Use `congrArg (fun f : Module.End L M => f m) he.1` as an intermediate fact. Simplify using `using this`. Set `i : P →ₗ[L] M` to `{ toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Set `s : M →ₗ[L] P` to `{ toFun := fun m => ⟨e m, m, rfl⟩ map_add' := fun x y => Subtype.ext (e.map_add x y) map_smul' := fun a m => Subtype.ext (e.map_smul a m) }`. Establish `hsi : s.comp i = LinearMap.id`.

Use extensionality with `⟨x, m, rfl⟩`. Conclude with `hee m`. Establish `hie : i.comp s = e`. Use extensionality with `m`. Both sides reduce to the same expression.

Establish `hei : e.comp i = i`. Use extensionality with `⟨x, m, rfl⟩`. Conclude with `hee m`. Use `haveI := h.free`. Use `haveI := h.fin`.

Use `haveI : Module.Projective L P := Module.Projective.of_split i s hsi`. Use `haveI : Module.Finite L P := Module.Finite.of_surjective s (fun x => ⟨i x, by`. Rewrite using `[← LinearMap.comp_apply, hsi, LinearMap.id_apply]⟩)`. Use `haveI : Module.Free L P := Module.free_of_flat_of_isLocalRing`. Set `J' : Ideal B` to `(Module.annihilator B P).radical`.

Establish `hD : Dat lam J' P` using `{ hs := hsP free := inferInstance fin := inferInstance rad := Ideal.radical_isRadical _ supp := fun p hp => hp.radical_le_iff.symm tf := by`. Introduce and unpack `c hc a ⟨n, hn⟩`. Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite `hn`, the goal using `[Module.mem_annihilator]`. Introduce `m`.

Establish `h1` using `hn m`. Rewrite `h1` using `[mul_pow, mul_smul, ← map_pow, ← hsP]`. Conclude with `(smul_eq_zero.mp h1).resolve_left (pow_ne_zero n hc) }`. Establish `hJ : J ≤ J'`. Establish `h0 : J ≤ (Module.annihilator B M).radical`.

Rewrite using `[Ideal.radical_eq_sInf]`. Conclude with `le_sInf fun p hp => (h.supp p hp.2).mp hp.1`. Use `h0.trans (Ideal.radical_mono ?_)` and prove the remaining obligations. Introduce `b hb`. Rewrite `hb`, the goal using `[Module.mem_annihilator]`.

Introduce `m`. Conclude with `Subtype.ext (hb m)`. Use `⟨J', P, inferInstance, inferInstance, inferInstance, hD, hJ, fun y => ?_⟩` and prove the remaining obligations. Use `letI : Algebra L K := ((y : B →+* K).comp (lam : L →+* B)).toAlgebra`. Set `F : B → Module.End K (K ⊗[L] M)` to `fun b => LinearMap.baseChange K (actL lam M h.hs b)`.

Set `G : B → Module.End K (K ⊗[L] P)` to `fun b => LinearMap.baseChange K (actL lam P hsP b)`. Set `E : Module.End K (K ⊗[L] M)` to `LinearMap.baseChange K e`. Set `ι : K ⊗[L] P →ₗ[K] K ⊗[L] M` to `LinearMap.baseChange K i`. Set `σ : K ⊗[L] M →ₗ[K] K ⊗[L] P` to `LinearMap.baseChange K s`. Establish `hσι : σ.comp ι = LinearMap.id`.

Simplify using `only [σ, ι, ← LinearMap.baseChange_comp, hsi, LinearMap.baseChange_id]`. Establish `hσιa : ∀ w, σ (ι w) = w` using `fun w => by`. Rewrite using `[← LinearMap.comp_apply, hσι, LinearMap.id_apply]`. Establish `hinj : Function.Injective ι` using `fun a b hab => by`. Rewrite using `[← hσιa a, hab, hσιa]`.

Establish `hισ : ι.comp σ = E`. Simplify using `only [ι, σ, E, ← LinearMap.baseChange_comp, hie]`. Establish `hEι : E.comp ι = ι`. Simplify using `only [ι, E, ← LinearMap.baseChange_comp, hei]`. Establish `hact : ∀ b, (actL lam M h.hs b).comp i = i.comp (actL lam P hsP b)` using `fun b => by`.

Use `ext`. Both sides reduce to the same expression. Establish `hFι : ∀ b (μ : K), (F b - μ • 1).comp ι = ι.comp (G b - μ • 1)` using `fun b μ => by`. Rewrite using `[LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul, Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]`. Use `congr 1`.

Simplify using `only [F, G, ι, ← LinearMap.baseChange_comp, hact]`. Establish `hpow : ∀ b (μ : K) (k : ℕ) w, ((F b - μ • 1) ^ k) (ι w) = ι (((G b - μ • 1) ^ k) w)` using `fun b μ k w => by`. Rewrite using `[← LinearMap.comp_apply, Module.End.commute_pow_left_of_commute (hFι b μ) k, LinearMap.comp_apply]`. Establish `key : (⨅ b, Module.End.maxGenEigenspace (G b) (y b)).map ι = (⨅ b, Module.End.maxGenEigenspace (F b) (y b)) ⊓ Module.End.eigenspace E 1`. Use extensionality with `v`.

Simplify using `only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff, one_smul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Use `⟨fun b => ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hw b`.

Conclude with `⟨k, by rw [hpow, hk, map_zero]⟩`. Rewrite using `[← LinearMap.comp_apply, hEι]`. Introduce and unpack `⟨hv, hE⟩`. Use `⟨σ v, fun b => ?_, ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `hv b`.

Use `⟨k, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[← hpow, ← LinearMap.comp_apply ι σ, hισ, hE, hk, map_zero]`. Rewrite using `[← LinearMap.comp_apply, hισ, hE]`. Establish `heq : mu lam P hD.hs y = muE lam M h.hs e y` using `by show Module.finrank K ↥(⨅ b, Module.End.maxGenEigenspace (G b) (y b)) = Module.finrank K ↥((⨅ b, Module.End.maxGenEigenspace (F b) (y b)) ⊓ Module.End.eigenspace E 1)`. Rewrite using `[← key]`.

Conclude with `(Submodule.equivMapOfInjective ι hinj _).finrank_eq`. Use `⟨heq, fun h1 => ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[← heq]`. Express the relevant statement in the definitionally equal form `1 ≤ Module.finrank K ↥(⨅ b, Module.End.maxGenEigenspace (G b) (y b)) at h1`. Establish `hne : (⨅ b, Module.End.maxGenEigenspace (G b) (y b)) ≠ ⊥` using `fun hbot => by`.

Rewrite `h1` using `[hbot, finrank_bot]`. Use linear arithmetic over natural numbers and integers. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Introduce and unpack `a ⟨n, hn⟩`. Rewrite using `[RingHom.mem_ker]`.

Assume the negation of the conclusion as `hya`. Establish `hpa : ∀ (n : ℕ) (m : P), (actL lam P hsP a ^ n) m = a ^ n • m`. Introduce `n m`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, one_smul]`.

Both sides reduce to the same expression. Consider the case `succ n ih => rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]`. Both sides reduce to the same expression. Establish `hGn : (G a) ^ n = 0`. Establish `h2 : actL lam P hsP a ^ n = 0`.

Use extensionality with `m`. Rewrite using `[hpa, LinearMap.zero_apply]`. Conclude with `congrArg Subtype.val ((Module.mem_annihilator.mp hn) m)`. Simplify using `only [G, ← LinearMap.baseChange_pow, h2, LinearMap.baseChange_zero]`. Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).mp (Submodule.mem_iInf _ |>.mp hw a)`.

Use `set c := y a with hc`. Establish `hX : IsUnit (c⁻¹ • G a - 1)` using `(IsNilpotent.smul ⟨n, hGn⟩ c⁻¹).isUnit_sub_one`. Establish `hGc : G a - c • 1 = c • (c⁻¹ • G a - 1)`. Rewrite using `[smul_sub, smul_smul, mul_inv_cancel₀ hya, one_smul]`. Rewrite `hk` using `[hGc, _root_.smul_pow, LinearMap.smul_apply]`.

Establish `hk2` using `(smul_eq_zero.mp hk).resolve_left (pow_ne_zero k hya)`. Establish `hinj2` using `(Module.End.isUnit_iff _).mp (hX.pow k)`. Conclude with `hw0 (hinj2.1 (by rw [hk2, map_zero]))`.
-/
theorem UpperTheory.V.Z.Desc.V0.muRange :
    MuRange := by
  unfold MuRange
  intro O L B K _ _ _ _ _ _ _ _ _ lam J M _ _ _ h e he
  letI : Algebra L B := (lam : L →+* B).toAlgebra
  haveI : IsScalarTower L B M := ⟨fun a b m => by
    rw [Algebra.smul_def, mul_smul, h.hs]
    rfl⟩
  let eB : M →ₗ[B] M :=
    { toFun := e, map_add' := e.map_add, map_smul' := fun b m => he.2 b m }
  let P : Submodule B M := LinearMap.range eB
  have hsP : ∀ (a : L) (m : P), a • m = lam a • m := fun a m => Subtype.ext (h.hs a m.1)
  have hee : ∀ m, e (e m) = e m := fun m => by
    have := congrArg (fun f : Module.End L M => f m) he.1
    simpa using this
  let i : P →ₗ[L] M :=
    { toFun := Subtype.val, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let s : M →ₗ[L] P :=
    { toFun := fun m => ⟨e m, m, rfl⟩
      map_add' := fun x y => Subtype.ext (e.map_add x y)
      map_smul' := fun a m => Subtype.ext (e.map_smul a m) }
  have hsi : s.comp i = LinearMap.id := by
    ext ⟨x, m, rfl⟩
    exact hee m
  have hie : i.comp s = e := by
    ext m
    rfl
  have hei : e.comp i = i := by
    ext ⟨x, m, rfl⟩
    exact hee m
  haveI := h.free
  haveI := h.fin
  haveI : Module.Projective L P := Module.Projective.of_split i s hsi
  haveI : Module.Finite L P := Module.Finite.of_surjective s (fun x => ⟨i x, by
    rw [← LinearMap.comp_apply, hsi, LinearMap.id_apply]⟩)
  haveI : Module.Free L P := Module.free_of_flat_of_isLocalRing
  let J' : Ideal B := (Module.annihilator B P).radical
  have hD : Dat lam J' P :=
    { hs := hsP
      free := inferInstance
      fin := inferInstance
      rad := Ideal.radical_isRadical _
      supp := fun p hp => hp.radical_le_iff.symm
      tf := by
        rintro c hc a ⟨n, hn⟩
        refine ⟨n, ?_⟩
        rw [Module.mem_annihilator] at hn ⊢
        intro m
        have h1 := hn m
        rw [mul_pow, mul_smul, ← map_pow, ← hsP] at h1
        exact (smul_eq_zero.mp h1).resolve_left (pow_ne_zero n hc) }
  have hJ : J ≤ J' := by
    have h0 : J ≤ (Module.annihilator B M).radical := by
      rw [Ideal.radical_eq_sInf]
      exact le_sInf fun p hp => (h.supp p hp.2).mp hp.1
    refine h0.trans (Ideal.radical_mono ?_)
    intro b hb
    rw [Module.mem_annihilator] at hb ⊢
    intro m
    exact Subtype.ext (hb m)
  refine ⟨J', P, inferInstance, inferInstance, inferInstance, hD, hJ, fun y => ?_⟩
  letI : Algebra L K := ((y : B →+* K).comp (lam : L →+* B)).toAlgebra
  let F : B → Module.End K (K ⊗[L] M) := fun b => LinearMap.baseChange K (actL lam M h.hs b)
  let G : B → Module.End K (K ⊗[L] P) := fun b => LinearMap.baseChange K (actL lam P hsP b)
  let E : Module.End K (K ⊗[L] M) := LinearMap.baseChange K e
  let ι : K ⊗[L] P →ₗ[K] K ⊗[L] M := LinearMap.baseChange K i
  let σ : K ⊗[L] M →ₗ[K] K ⊗[L] P := LinearMap.baseChange K s
  have hσι : σ.comp ι = LinearMap.id := by
    simp only [σ, ι, ← LinearMap.baseChange_comp, hsi, LinearMap.baseChange_id]
  have hσιa : ∀ w, σ (ι w) = w := fun w => by
    rw [← LinearMap.comp_apply, hσι, LinearMap.id_apply]
  have hinj : Function.Injective ι := fun a b hab => by
    rw [← hσιa a, hab, hσιa]
  have hισ : ι.comp σ = E := by
    simp only [ι, σ, E, ← LinearMap.baseChange_comp, hie]
  have hEι : E.comp ι = ι := by
    simp only [ι, E, ← LinearMap.baseChange_comp, hei]
  have hact : ∀ b, (actL lam M h.hs b).comp i = i.comp (actL lam P hsP b) := fun b => by
    ext
    rfl
  have hFι : ∀ b (μ : K), (F b - μ • 1).comp ι = ι.comp (G b - μ • 1) := fun b μ => by
    rw [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul,
      Module.End.one_eq_id, Module.End.one_eq_id, LinearMap.id_comp, LinearMap.comp_id]
    congr 1
    simp only [F, G, ι, ← LinearMap.baseChange_comp, hact]
  have hpow : ∀ b (μ : K) (k : ℕ) w,
      ((F b - μ • 1) ^ k) (ι w) = ι (((G b - μ • 1) ^ k) w) :=
    fun b μ k w => by
      rw [← LinearMap.comp_apply, Module.End.commute_pow_left_of_commute (hFι b μ) k,
        LinearMap.comp_apply]
  have key : (⨅ b, Module.End.maxGenEigenspace (G b) (y b)).map ι =
      (⨅ b, Module.End.maxGenEigenspace (F b) (y b)) ⊓ Module.End.eigenspace E 1 := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_iInf,
      Module.End.mem_maxGenEigenspace, Module.End.mem_eigenspace_iff, one_smul]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨fun b => ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hw b
        exact ⟨k, by rw [hpow, hk, map_zero]⟩
      · rw [← LinearMap.comp_apply, hEι]
    · rintro ⟨hv, hE⟩
      refine ⟨σ v, fun b => ?_, ?_⟩
      · obtain ⟨k, hk⟩ := hv b
        refine ⟨k, hinj ?_⟩
        rw [← hpow, ← LinearMap.comp_apply ι σ, hισ, hE, hk, map_zero]
      · rw [← LinearMap.comp_apply, hισ, hE]
  have heq : mu lam P hD.hs y = muE lam M h.hs e y := by
    show Module.finrank K ↥(⨅ b, Module.End.maxGenEigenspace (G b) (y b)) =
      Module.finrank K ↥((⨅ b, Module.End.maxGenEigenspace (F b) (y b)) ⊓ Module.End.eigenspace E 1)
    rw [← key]
    exact (Submodule.equivMapOfInjective ι hinj _).finrank_eq
  refine ⟨heq, fun h1 => ?_⟩
  rw [← heq] at h1
  change 1 ≤ Module.finrank K ↥(⨅ b, Module.End.maxGenEigenspace (G b) (y b)) at h1
  have hne : (⨅ b, Module.End.maxGenEigenspace (G b) (y b)) ≠ ⊥ := fun hbot => by
    rw [hbot, finrank_bot] at h1
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rintro a ⟨n, hn⟩
  rw [RingHom.mem_ker]
  by_contra hya
  have hpa : ∀ (n : ℕ) (m : P), (actL lam P hsP a ^ n) m = a ^ n • m := by
    intro n m
    induction n with
    | zero => rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, pow_succ', mul_smul]; rfl
  have hGn : (G a) ^ n = 0 := by
    have h2 : actL lam P hsP a ^ n = 0 := by
      ext m
      rw [hpa, LinearMap.zero_apply]
      exact congrArg Subtype.val ((Module.mem_annihilator.mp hn) m)
    simp only [G, ← LinearMap.baseChange_pow, h2, LinearMap.baseChange_zero]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp (Submodule.mem_iInf _ |>.mp hw a)
  set c := y a with hc
  have hX : IsUnit (c⁻¹ • G a - 1) := (IsNilpotent.smul ⟨n, hGn⟩ c⁻¹).isUnit_sub_one
  have hGc : G a - c • 1 = c • (c⁻¹ • G a - 1) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hya, one_smul]
  rw [hGc, _root_.smul_pow, LinearMap.smul_apply] at hk
  have hk2 := (smul_eq_zero.mp hk).resolve_left (pow_ne_zero k hya)
  have hinj2 := (Module.End.isUnit_iff _).mp (hX.pow k)
  exact hw0 (hinj2.1 (by rw [hk2, map_zero]))
