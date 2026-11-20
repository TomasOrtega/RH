import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.BaseMatrixAlgebra
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FormCoreSKXOf

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems

/- English proof (translation)
Use `set V := dualWeyl Kf (m + 1) (m + 1) (nuOf lam) with hV`. Take `⟨Z0, -⟩` from `latBasis (O := O) hinj m lam 1 (by simp)`. Establish `hfinI : Finite ↥(ssIdx (m + 1) (m + 1) (nuOf lam))` using `(sSIdxFinite (m + 1) (m + 1) (nuOf lam)).to_subtype`. Establish `hfd : FiniteDimensional Kf V` using `Module.Finite.of_basis Z0`. Set `β0 : V →ₗ[Kf] Module.Dual Kf V` to `LinearMap.mk₂ Kf (fun (Q P : V) => B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q) (by intro Q Q' P; simp) (by intro c Q P; simp) (by intro Q P P'; simp) (by intro c Q P; simp)`.

Establish `hβ0 : ∀ Q P : V, β0 Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q` using `fun _ _ => rfl`. Establish `hinjβ : Function.Injective β0`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `Q hQ`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hb _ Q.2` to reduce the goal to its premises. Introduce `P hP`. Use `congrArg (fun f => f ⟨P, hP⟩) hQ` as an intermediate fact. Conclude with `this`. Set `β : V ≃ₗ[Kf] Module.Dual Kf V` to `LinearMap.linearEquivOfInjective β0 hinjβ Subspace.dual_finrank_eq.symm`.

Establish `hβ : ∀ Q P : V, β Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q` using `fun _ _ => rfl`. Use `set e : ℤ := lam (Fin.last m) with he`. Establish `key : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det → ∀ P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf, B (M.det ^ e • rowAct Kf M P) (((M⁻¹).transpose).det ^ e • rowAct Kf (M⁻¹).transpose Q) = B P Q`. Introduce `M hM P Q`. Rewrite using `[map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul, mul_comm (((M⁻¹).transpose).det ^ e), det_invT_zpow M hM e, one_mul, ← ha, ldlat_rowAct_inv_right rowActMul M hM]`.

Establish `mem_iff : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det → ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf, F ∈ nablaLTw O Kf m lam M ↔ M.det ^ e • rowAct Kf M F ∈ nabO O Kf m (nuOf lam)` using `fun M hM F => nablaLTwMem O Kf m lam M hM F`. Use `⟨β, ⟨?_, ?_⟩, hβ⟩` and prove the remaining obligations. Introduce `M hM Q hQ`. Rewrite using `[mem_iff _ (det_invT M hM)]`. Apply `hc` to reduce the goal to its premises.

Conclude with `Submodule.smul_mem _ _ (dualWeylRowStable Kf _ _ _ _ _ Q.2)`. Introduce `P0 hP0 set P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf := M.det ^ (-e) • rowAct Kf M⁻¹ P0 with hP`. Establish `h1 : M.det ^ e • rowAct Kf M P = P0`. Rewrite using `[hP, map_smul, smul_smul, ← zpow_add₀ hM.ne_zero, add_neg_cancel, zpow_zero, one_smul, ldlat_rowAct_inv_left rowActMul M hM]`. Establish `h2 : P ∈ nablaLTw O Kf m lam M`.

Rewrite using `[mem_iff M hM, h1]`. Conclude with `hP0`. Establish `h3` using `hQ ⟨P, la_nablaLTw_le m lam M hM P h2⟩ h2`. Rewrite `h3` using `[hβ, ← key M hM, h1]`. Conclude with `h3`.

Introduce `M hM Q P hQ hP`. Rewrite using `[hβ]`. Establish `h1` using `(mem_iff M hM _).1 hP`. Establish `h2` using `(mem_iff _ (det_invT M hM) _).1 hQ`. Establish `h3` using `hdd _ h2 _ h1`.

Rewrite `h3` using `[map_smul, key M hM]`. Rewrite using `[Submodule.coe_smul, map_smul]`. Conclude with `h3`.
-/
theorem posCore_of_formX {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (p m : ℕ) (lam : Fin (m + 1) → ℤ) (N : ℕ)
    (B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf →ₗ[Kf] Kf)
    (ha : ∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
        B (rowAct Kf g P) Q = B P (rowAct Kf g.transpose Q))
    (hb : ∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam), B P Q = 0) → Q = 0)
    (hc : ∀ Q ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf lam),
        (∀ P ∈ nabO O Kf m (nuOf lam), B P Q ∈ Set.range (algebraMap O Kf)) → Q ∈ nabO O Kf m (nuOf lam))
    (hdd : ∀ Q ∈ nabO O Kf m (nuOf lam), ∀ P ∈ nabO O Kf m (nuOf lam),
        B P (((p : Kf) ^ N) • Q) ∈ Set.range (algebraMap O Kf)) :
    ∃ β, PosCore O Kf p m lam N β ∧ ∀ Q P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf lam)),
      β Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) := by
  classical
  set V := dualWeyl Kf (m + 1) (m + 1) (nuOf lam) with hV
  obtain ⟨Z0, -⟩ := latBasis (O := O) hinj m lam 1 (by simp)
  have hfinI : Finite ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite (m + 1) (m + 1) (nuOf lam)).to_subtype
  have hfd : FiniteDimensional Kf V := Module.Finite.of_basis Z0
  let β0 : V →ₗ[Kf] Module.Dual Kf V :=
    LinearMap.mk₂ Kf (fun (Q P : V) => B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q)
      (by intro Q Q' P; simp)
      (by intro c Q P; simp)
      (by intro Q P P'; simp)
      (by intro c Q P; simp)
  have hβ0 : ∀ Q P : V, β0 Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q := fun _ _ => rfl
  have hinjβ : Function.Injective β0 := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Q hQ
    apply Subtype.ext
    apply hb _ Q.2
    intro P hP
    have := congrArg (fun f => f ⟨P, hP⟩) hQ
    exact this
  let β : V ≃ₗ[Kf] Module.Dual Kf V := LinearMap.linearEquivOfInjective β0 hinjβ Subspace.dual_finrank_eq.symm
  have hβ : ∀ Q P : V, β Q P = B (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) Q := fun _ _ => rfl
  set e : ℤ := lam (Fin.last m) with he
  have key : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det →
      ∀ P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      B (M.det ^ e • rowAct Kf M P) (((M⁻¹).transpose).det ^ e • rowAct Kf (M⁻¹).transpose Q) = B P Q := by
    intro M hM P Q
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, smul_eq_mul, mul_comm (((M⁻¹).transpose).det ^ e),
      det_invT_zpow M hM e, one_mul, ← ha, ldlat_rowAct_inv_right rowActMul M hM]
  have mem_iff : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf), IsUnit M.det →
      ∀ F : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf,
      F ∈ nablaLTw O Kf m lam M ↔ M.det ^ e • rowAct Kf M F ∈ nabO O Kf m (nuOf lam) :=
    fun M hM F => nablaLTwMem O Kf m lam M hM F
  refine ⟨β, ⟨?_, ?_⟩, hβ⟩
  · intro M hM Q hQ
    rw [mem_iff _ (det_invT M hM)]
    apply hc
    · exact Submodule.smul_mem _ _ (dualWeylRowStable Kf _ _ _ _ _ Q.2)
    · intro P0 hP0
      set P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf := M.det ^ (-e) • rowAct Kf M⁻¹ P0 with hP
      have h1 : M.det ^ e • rowAct Kf M P = P0 := by
        rw [hP, map_smul, smul_smul, ← zpow_add₀ hM.ne_zero, add_neg_cancel, zpow_zero, one_smul,
          ldlat_rowAct_inv_left rowActMul M hM]
      have h2 : P ∈ nablaLTw O Kf m lam M := by
        rw [mem_iff M hM, h1]; exact hP0
      have h3 := hQ ⟨P, la_nablaLTw_le m lam M hM P h2⟩ h2
      rw [hβ, ← key M hM, h1] at h3
      exact h3
  · intro M hM Q P hQ hP
    rw [hβ]
    have h1 := (mem_iff M hM _).1 hP
    have h2 := (mem_iff _ (det_invT M hM) _).1 hQ
    have h3 := hdd _ h2 _ h1
    rw [map_smul, key M hM] at h3
    rw [Submodule.coe_smul, map_smul]
    exact h3

/- English proof (translation)
Substitute `hVs` using the available equality. Establish `hinj : Function.Injective (algebraMap O Kf)` using `IsFractionRing.injective O Kf`. Establish `hanti` using `kp_lamAt_antitone lam0 hd`. Establish `hfin : ∀ s : Fin n', Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))` using `fun s => (sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).to_subtype`. Set `_ : ∀ s : Fin n', Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))` to `fun s => Fintype.ofFinite _`.

Use `set V : Fin n' → Submodule Kf (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) := fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) with hV`. Establish `hb` using `fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) 1 (by simp)`. Use `choose b _ using hb`. Take `⟨Ψ, hΨ⟩` from `psi_exists V β b`. Use `⟨Ψ, ?_, fun Ms hMs => ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `prodBasis V b`. Take `⟨x', hx'⟩` from `prodBasis V (fun s => dualB (β s) (b s))`. Establish `h1 : ∀ j, Ψ.symm (x' j) = x.coord j` using `fun j => by`. Rewrite using `[← hΨ b x x' hx hx' j, LinearEquiv.symm_apply_apply]`. Establish `hpure : ∀ (Q P : ∀ s, V s) (y u : tensorLat Kf Kf V), (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ∏ s, blockEmb Kf s ((Q s : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) → (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ∏ s, blockEmb Kf s …`.

Introduce `Q P y u hy hu`. Establish `h2 : y = ∑ i, (∏ s, β s (Q s) (b s (i s))) • x' i` using `by conv_lhs => rw [← x'.sum_repr y]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[repr_prod V (fun s => dualB (β s) (b s)) x' hx' Q y hy i]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun s _ => dualB_repr (β s) (b s) (Q s) (i s)`. Establish `h3 : ∀ i, x.repr u i = ∏ s, (b s).repr (P s) (i s)` using `fun i => repr_prod V b x hx P u hu i`. Rewrite using `[h2, map_sum, LinearMap.sum_apply]`. Simplify using `only [map_smul, LinearMap.smul_apply, h1, Module.Basis.coord_apply, smul_eq_mul, h3, ← Finset.prod_mul_distrib]`. Rewrite using `[← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun s a => β s (Q s) (b s a) * (b s).repr (P s) a)]`.

Use `Finset.prod_congr rfl fun s _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← (b s).sum_repr (P s)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.

Establish `hB` using `TS.fock_pairing_bilinear`. Set `Bc` to `TS.tscForm hB (K := Kf) (σ := Fin n' × (Fin (m + 1) × Fin (m + 1))) ((∏ s, cs s)⁻¹)`. Set `Φ2 : (tensorLat Kf Kf V) →ₗ[Kf] Module.Dual Kf (tensorLat Kf Kf V)` to `LinearMap.mk₂ Kf (fun (y u : tensorLat Kf Kf V) => Bc (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) y) (by intro Q Q' P; simp) (by intro c Q P; simp) (by intro Q P P'; simp) (by intro c Q P; simp)`. Establish `hΦ : ∀ y u : tensorLat Kf Kf V, Φ2 y u = (∏ s, cs s) * TS.fockR (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)`. Introduce `y u`.

Use `show ((∏ s, cs s)⁻¹)⁻¹ * TS.fockR _ _ = _`. Rewrite using `[inv_inv]`. Establish `hEq : Ψ.symm.toLinearMap = Φ2`. Use `x.ext fun i => x.ext fun j => ?_` and prove the remaining obligations. Use `show Ψ.symm (x i) (x j) = Φ2 (x i) (x j)`.

Rewrite using `[hΦ, hpure (fun s => b s (i s)) (fun s => b s (j s)) (x i) (x j) (hx i) (hx j), hx i, hx j, TS.fock_pairing_block Kf (Fin n') (m + 1) (m + 1), ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun s _ => hcs s _ _`. Introduce `y u`. Rewrite using `[← hΦ]`. Conclude with `congrArg (fun f => f y u) hEq`.

Establish `hMs' : ∀ s, IsUnit (((Ms s)⁻¹).transpose).det` using `fun s => det_invT _ (hMs s)`. Establish `hZ` using `fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) (Ms s) (hMs s)`. Use `choose Z hZ using hZ`. Take `⟨z, hz⟩` from `prodBasis V Z`. Take `⟨z', hz'⟩` from `prodBasis V (fun s => dualB (β s) (Z s))`.

Establish `hH : ∀ Ns : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ns s).det) → Hten O lam0 (fun s => colSpan O (Ns s)) = tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) (Ns s))`. Introduce `Ns hNs`. Unfold `Hten`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Rewrite using `[H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _ (hNs s)]`. Establish `hΛ : (Hten O lam0 fun s => colSpan O (Ms s)).comap ((tensorLat Kf Kf V).subtype.restrictScalars O) = Submodule.span O (Set.range z)`. Take `⟨-, oS⟩` from `tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ _ (fun s i => ((Z s i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)) (fun s => li_coe hinj (V s) (Z s)) hZ`. Rewrite using `[hH Ms hMs, ← oS, ← comap_span_coe]`. Use `congr 3`.

Use function extensionality and compare the values at `i`. Conclude with `(hz i).symm`. Establish `hdual : dualLat O Kf (Submodule.span O (Set.range z)) = Submodule.span O (Set.range fun i => z.coord i)`. Use `dualLat_span (O := O) z (fun _ => 1) (fun _ => one_ne_zero)` as an intermediate fact. Simplify using `using this`.

Establish `hmap : (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap ((tensorLat Kf Kf V).subtype.restrictScalars O))).map (Ψ.toLinearMap.restrictScalars O) = Submodule.span O (Set.range z')`. Rewrite using `[hΛ, hdual, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `j`. Conclude with `hΨ Z z z' hz hz' j`.

Rewrite using `[hmap]`. Establish `hPmem : ∀ s (P : V s), (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈ nablaLTw O Kf m (lamAt lam0 s) (Ms s) → P ∈ Submodule.span O (Set.range (Z s))`. Introduce `s P hP`. Rewrite `hP` using `[← hZ s]`. Rewrite using `[← comap_span_coe]`.

Conclude with `hP`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show ((z' j : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose`.

Rewrite using `[hz', hH _ hMs']`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨fun s => ((dualB (β s) (Z s) (j s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf), fun s => ?_, rfl⟩` and prove the remaining obligations. Apply `(hβ s).up (Ms s) (hMs s)` to reduce the goal to its premises. Introduce `P hP`.

Rewrite using `[beta_dualB, Module.Basis.coord_apply]`. Conclude with `repr_int (Z s) P (hPmem s P hP) (j s)`. Introduce and unpack `_ ⟨Q, hQ, rfl⟩ show ((p : Kf) ^ (∑ s, N s)) • Q ∈ Submodule.span O (Set.range z')`. Rewrite using `[← comap_span_coe]`. Use `show ((((p : Kf) ^ (∑ s, N s)) • Q : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Submodule.span O (Set.range fun i => ((z' i : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))`.

Take `⟨-, oS'⟩` from `tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ (fun s => Submodule.span O (Set.range fun i => ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))) (fun s i => ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)) (fun s => li_coe hinj …`. Establish `hr : (Set.range fun i => ((z' i : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) = Set.range fun i : (∀ s, ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) => ∏ s, blockEmb Kf s ((dualB (β s) (Z s) (i s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + …`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hz' i`.

Rewrite using `[hr, oS', Submodule.coe_smul, ← Finset.prod_pow_eq_pow_sum]`. Establish `hQ' : (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) ((Ms s)⁻¹).transpose)`. Rewrite using `[← hH _ hMs']`. Conclude with `hQ`. Use `lb_tensor O Kf _ _ (fun s => (p : Kf) ^ N s) (fun s F hF => ?_) _ hQ'` and prove the remaining obligations.

Establish `hFV : F ∈ V s` using `la_nablaLTw_le m (lamAt lam0 s) _ (hMs' s) F hF`. Establish `h1 : (((p : Kf) ^ N s) • (⟨F, hFV⟩ : V s)) ∈ Submodule.span O (Set.range fun i => (1 : Kf) • dualB (β s) (Z s) i)`. Apply `mem_span_of_coord (dualB (β s) (Z s)) (fun _ => 1) (fun _ => one_ne_zero)` to reduce the goal to its premises. Introduce `i`. Rewrite using `[inv_one, one_mul, Module.Basis.coord_apply, dualB_repr]`.

Apply `(hβ s).low (Ms s) (hMs s) ⟨F, hFV⟩ (Z s i) hF` to reduce the goal to its premises. Rewrite using `[← hZ s]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Simplify using `only [one_smul] at h1`. Rewrite `h1` using `[← comap_span_coe]`.

Conclude with `h1`.
-/
theorem ten_sideX (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    (p : ℕ) {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0) (N : Fin n' → ℕ)
    (β : ∀ s : Fin n', ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) ≃ₗ[Kf]
      Module.Dual Kf ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))))
    (hβ : ∀ s, PosCore O Kf p m (lamAt lam0 s) (N s) (β s))
    (cs : Fin n' → Kf) (hcs : ∀ s (Q P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)))), β s Q P =
      cs s * TS.fockR (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
    (Vs : Submodule Kf (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
    (hVs : Vs = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) :
    ∃ Ψ : Module.Dual Kf Vs ≃ₗ[Kf] Vs,
      (∀ y u : Vs, Ψ.symm y u = (∏ s, cs s) * TS.fockR (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
        (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) ∧
      ∀ Ms : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ms s).det) →
        (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap (Vs.subtype.restrictScalars O))).map
            (Ψ.toLinearMap.restrictScalars O) ≤
          (Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose).comap (Vs.subtype.restrictScalars O) ∧
        scale ((p : Kf) ^ (∑ s, N s))
            ((Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose).comap (Vs.subtype.restrictScalars O)) ≤
          (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap (Vs.subtype.restrictScalars O))).map
            (Ψ.toLinearMap.restrictScalars O) := by
  subst hVs
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hanti := kp_lamAt_antitone lam0 hd
  have hfin : ∀ s : Fin n', Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite (m + 1) (m + 1) (nuOf (lamAt lam0 s))).to_subtype
  let _ : ∀ s : Fin n', Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := fun s => Fintype.ofFinite _
  set V : Fin n' → Submodule Kf (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
    fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)) with hV
  have hb := fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) 1 (by simp)
  choose b _ using hb
  obtain ⟨Ψ, hΨ⟩ := psi_exists V β b
  refine ⟨Ψ, ?_, fun Ms hMs => ?_⟩
  · obtain ⟨x, hx⟩ := prodBasis V b
    obtain ⟨x', hx'⟩ := prodBasis V (fun s => dualB (β s) (b s))
    have h1 : ∀ j, Ψ.symm (x' j) = x.coord j := fun j => by
      rw [← hΨ b x x' hx hx' j, LinearEquiv.symm_apply_apply]
    have hpure : ∀ (Q P : ∀ s, V s) (y u : tensorLat Kf Kf V),
        (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ∏ s, blockEmb Kf s ((Q s : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) →
        (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) =
          ∏ s, blockEmb Kf s ((P s : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) →
        Ψ.symm y u = ∏ s, β s (Q s) (P s) := by
      intro Q P y u hy hu
      have h2 : y = ∑ i, (∏ s, β s (Q s) (b s (i s))) • x' i := by
        conv_lhs => rw [← x'.sum_repr y]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [repr_prod V (fun s => dualB (β s) (b s)) x' hx' Q y hy i]
        congr 1
        exact Finset.prod_congr rfl fun s _ => dualB_repr (β s) (b s) (Q s) (i s)
      have h3 : ∀ i, x.repr u i = ∏ s, (b s).repr (P s) (i s) := fun i => repr_prod V b x hx P u hu i
      rw [h2, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, h1, Module.Basis.coord_apply, smul_eq_mul, h3,
        ← Finset.prod_mul_distrib]
      rw [← Fintype.piFinset_univ,
        ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun s a => β s (Q s) (b s a) * (b s).repr (P s) a)]
      refine Finset.prod_congr rfl fun s _ => ?_
      conv_rhs => rw [← (b s).sum_repr (P s)]
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hB := TS.fock_pairing_bilinear
    let Bc := TS.tscForm hB (K := Kf) (σ := Fin n' × (Fin (m + 1) × Fin (m + 1))) ((∏ s, cs s)⁻¹)
    let Φ2 : (tensorLat Kf Kf V) →ₗ[Kf] Module.Dual Kf (tensorLat Kf Kf V) :=
      LinearMap.mk₂ Kf (fun (y u : tensorLat Kf Kf V) => Bc (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) y)
        (by intro Q Q' P; simp)
        (by intro c Q P; simp)
        (by intro Q P P'; simp)
        (by intro c Q P; simp)
    have hΦ : ∀ y u : tensorLat Kf Kf V, Φ2 y u = (∏ s, cs s) * TS.fockR (u : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)
        (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := by
      intro y u
      show ((∏ s, cs s)⁻¹)⁻¹ * TS.fockR _ _ = _
      rw [inv_inv]
    have hEq : Ψ.symm.toLinearMap = Φ2 := by
      refine x.ext fun i => x.ext fun j => ?_
      show Ψ.symm (x i) (x j) = Φ2 (x i) (x j)
      rw [hΦ, hpure (fun s => b s (i s)) (fun s => b s (j s)) (x i) (x j) (hx i) (hx j), hx i, hx j,
        TS.fock_pairing_block Kf (Fin n') (m + 1) (m + 1), ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun s _ => hcs s _ _
    intro y u
    rw [← hΦ]
    exact congrArg (fun f => f y u) hEq
  have hMs' : ∀ s, IsUnit (((Ms s)⁻¹).transpose).det := fun s => det_invT _ (hMs s)
  have hZ := fun s : Fin n' => latBasis (O := O) hinj m (lamAt lam0 s) (Ms s) (hMs s)
  choose Z hZ using hZ
  obtain ⟨z, hz⟩ := prodBasis V Z
  obtain ⟨z', hz'⟩ := prodBasis V (fun s => dualB (β s) (Z s))
  have hH : ∀ Ns : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf, (∀ s, IsUnit (Ns s).det) →
      Hten O lam0 (fun s => colSpan O (Ns s)) =
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) (Ns s)) := by
    intro Ns hNs
    unfold Hten
    congr 1
    funext s
    rw [H0_eq_twisted_nabla (la_indep hinj) _ _ (hanti s) _ (hNs s)]

  have hΛ : (Hten O lam0 fun s => colSpan O (Ms s)).comap ((tensorLat Kf Kf V).subtype.restrictScalars O) =
      Submodule.span O (Set.range z) := by
    obtain ⟨-, oS⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ _
      (fun s i => ((Z s i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
      (fun s => li_coe hinj (V s) (Z s)) hZ
    rw [hH Ms hMs, ← oS, ← comap_span_coe]
    congr 3
    funext i
    exact (hz i).symm
  have hdual : dualLat O Kf (Submodule.span O (Set.range z)) =
      Submodule.span O (Set.range fun i => z.coord i) := by
    have := dualLat_span (O := O) z (fun _ => 1) (fun _ => one_ne_zero)
    simpa using this
  have hmap : (dualLat O Kf ((Hten O lam0 fun s => colSpan O (Ms s)).comap
      ((tensorLat Kf Kf V).subtype.restrictScalars O))).map (Ψ.toLinearMap.restrictScalars O) =
      Submodule.span O (Set.range z') := by
    rw [hΛ, hdual, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hΨ Z z z' hz hz' j
  rw [hmap]
  have hPmem : ∀ s (P : V s), (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) ∈
      nablaLTw O Kf m (lamAt lam0 s) (Ms s) → P ∈ Submodule.span O (Set.range (Z s)) := by
    intro s P hP
    rw [← hZ s] at hP
    rw [← comap_span_coe]
    exact hP
  constructor
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show ((z' j : tensorLat Kf Kf V) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
      Hten O lam0 fun s => colSpan O ((Ms s)⁻¹).transpose
    rw [hz', hH _ hMs']
    apply Submodule.subset_span
    refine ⟨fun s => ((dualB (β s) (Z s) (j s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf),
      fun s => ?_, rfl⟩
    apply (hβ s).up (Ms s) (hMs s)
    intro P hP
    rw [beta_dualB, Module.Basis.coord_apply]
    exact repr_int (Z s) P (hPmem s P hP) (j s)
  · rintro _ ⟨Q, hQ, rfl⟩
    show ((p : Kf) ^ (∑ s, N s)) • Q ∈ Submodule.span O (Set.range z')
    rw [← comap_span_coe]
    show ((((p : Kf) ^ (∑ s, N s)) • Q : tensorLat Kf Kf V) :
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
      Submodule.span O (Set.range fun i => ((z' i : tensorLat Kf Kf V) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf))
    obtain ⟨-, oS'⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _
      (fun s => Submodule.span O (Set.range fun i =>
        ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)))
      (fun s i => ((dualB (β s) (Z s) i : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf))
      (fun s => li_coe hinj (V s) (dualB (β s) (Z s))) (fun s => rfl)
    have hr : (Set.range fun i => ((z' i : tensorLat Kf Kf V) :
        MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)) =
        Set.range fun i : (∀ s, ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) =>
          ∏ s, blockEmb Kf s ((dualB (β s) (Z s) (i s) : V s) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) := by
      congr 1
      funext i
      exact hz' i
    rw [hr, oS', Submodule.coe_smul, ← Finset.prod_pow_eq_pow_sum]
    have hQ' : (Q : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        tensorLat O Kf (fun s => nablaLTw O Kf m (lamAt lam0 s) ((Ms s)⁻¹).transpose) := by
      rw [← hH _ hMs']
      exact hQ
    refine lb_tensor O Kf _ _ (fun s => (p : Kf) ^ N s) (fun s F hF => ?_) _ hQ'
    have hFV : F ∈ V s := la_nablaLTw_le m (lamAt lam0 s) _ (hMs' s) F hF
    have h1 : (((p : Kf) ^ N s) • (⟨F, hFV⟩ : V s)) ∈
        Submodule.span O (Set.range fun i => (1 : Kf) • dualB (β s) (Z s) i) := by
      apply mem_span_of_coord (dualB (β s) (Z s)) (fun _ => 1) (fun _ => one_ne_zero)
      intro i
      rw [inv_one, one_mul, Module.Basis.coord_apply, dualB_repr]
      apply (hβ s).low (Ms s) (hMs s) ⟨F, hFV⟩ (Z s i) hF
      rw [← hZ s]
      exact Submodule.subset_span ⟨i, rfl⟩
    simp only [one_smul] at h1
    rw [← comap_span_coe] at h1
    exact h1

/- English proof (translation)
Introduce `p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd`. Use `h.frac_O` as an intermediate fact. Establish `hinj : Function.Injective (algebraMap O Kf)` using `IsFractionRing.injective O Kf`. Establish `hanti` using `kp_lamAt_antitone lam0 hd`. Establish `hpos : ∀ s : Fin n', ∃ β, PosCore O Kf p m (lamAt lam0 s) (expN p m (lamAt lam0 s)) β ∧ ∃ c : Kf, c ≠ 0 ∧ ∀ Q P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))), β Q P = c * TS.fockR (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin (m + 1) × Fin (m + …`.

Introduce `s`. Take `⟨B, ⟨c, hc0, hcB⟩, ha, hb, hc, hdd⟩` from `TS.formCoreSKX p n' W Qq O Kf ι σ j w h m (lamAt lam0 s) (hanti s)`. Take `⟨β, h1, h2⟩` from `posCore_of_formX hinj p m (lamAt lam0 s) _ B ha hb hc hdd`. Conclude with `⟨β, h1, c, hc0, fun Q P => by rw [h2, hcB]⟩`. Use `choose β hβ cs hcs0 hcs using hpos`.

Establish `hV : Vsp Kf lam0 = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s)))`. Unfold `Vsp`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[if_pos (hanti s)]`.

Take `⟨Ψ, hform, hΨ⟩` from `ten_sideX O Kf p lam0 hd (fun s => expN p m (lamAt lam0 s)) β hβ cs hcs (Vsp Kf lam0) hV`. Establish `hκ : (p : Kf) ^ ((kap1 p lam0 : ℕ) : ℤ) = (p : Kf) ^ (∑ s, expN p m (lamAt lam0 s))`. Rewrite using `[zpow_natCast]`. Both sides reduce to the same expression. Use `⟨Ψ, ∏ s, cs s, Finset.prod_ne_zero_iff.2 (fun s _ => hcs0 s), ?_, hform⟩` and prove the remaining obligations.

Unfold `Formalism.MainNotions.TestSideCounting.TSProp`. Rewrite using `[hκ]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `L hL`. Take `⟨g, hg, rfl⟩` from `hL`.

Establish `h1` using `hΨ (fun s => la_tw ι σ s.val g) (fun s => la_tw_det _ _ _ g hg)`. Establish `e1 : HL (O` using `O) ι σ lam0 (colSpan W g) = (Hten O lam0 fun s => colSpan O (la_tw ι σ s.val g)).comap ((Vsp Kf lam0).subtype.restrictScalars O) := by`. Unfold `HL toV`. Simplify using `only [extO_colSpan h]`. Establish `e2 : HL (O` using `O) ι σ lam0 (latDual (colSpan W g)) = (Hten O lam0 fun s => colSpan O ((la_tw ι σ s.val g)⁻¹).transpose).comap ((Vsp Kf lam0).subtype.restrictScalars O) := by`.

Unfold `HL toV`. Rewrite using `[latDual_colSpan g hg]`. Simplify using `only [extO_colSpan h, tw_invT ι σ _ g hg]`. Rewrite using `[e1, e2]`. Conclude with `h1`.

Introduce `e he`. Take `⟨g, hgb⟩` from `edgeBasis h m r e he`. Establish `hg` using `hgb.1`. Establish `hw` using `w_ne h`. Establish `hp` using `p_eq h`.

Use `set c : Kf := algebraMap O Kf w with hc`. Establish `hN : ∀ s : Fin n', IsUnit (la_tw ι σ s.val g * lb_D (m + 1) r c).det`. Introduce `s`. Rewrite using `[Matrix.det_mul]`. Conclude with `(la_tw_det _ _ _ g hg).mul (lb_D_det _ _ _ hw)`.

Establish `h1` using `hΨ (fun s => la_tw ι σ s.val g * lb_D (m + 1) r c) hN`. Establish `e1 : HLe (O` using `O) p ι σ w lam0 e = (Hten O lam0 fun s => colSpan O (la_tw ι σ s.val g * lb_D (m + 1) r c)).comap ((Vsp Kf lam0).subtype.restrictScalars O) := by`. Unfold `HLe toV`. Simplify using `only [leAt_of_basis h m r e g hgb, ← hc]`. Establish `e2 : HLe (O` using `O) p ι σ w lam0 e.dual = (Hten O lam0 fun s => colSpan O ((la_tw ι σ s.val g * lb_D (m + 1) r c)⁻¹).transpose).comap ((Vsp Kf lam0).subtype.restrictScalars O) := by`.

Unfold `HLe toV`. Simplify using `only [leAt_of_basis h m r e.dual _ (dual_edgeBasis p r (pQ_ne h) e g hgb), tw_mul, tw_invT ι σ _ g hg, tw_dE, invT_mul_D _ (la_tw_det ι σ _ g hg) r c hw, Matrix.mul_assoc, hp, ← hc, dE_sq_D r c hw]`. Unfold `Re Re'`. Rewrite using `[e1, e2, scale_map, scale_comm]`. Conclude with `⟨scale_mono _ h1.1, scale_mono _ h1.2⟩`.
-/
theorem test_side_explicit_identification : Formalism.MainNotions.TestSideCounting.RestTSX := by
  intro p n' W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w h m r lam0 hd
  have := h.frac_O
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hanti := kp_lamAt_antitone lam0 hd
  have hpos : ∀ s : Fin n', ∃ β, PosCore O Kf p m (lamAt lam0 s) (expN p m (lamAt lam0 s)) β ∧ ∃ c : Kf, c ≠ 0 ∧
      ∀ Q P : ↥(dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))), β Q P =
        c * TS.fockR (P : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) (Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) := by
    intro s
    obtain ⟨B, ⟨c, hc0, hcB⟩, ha, hb, hc, hdd⟩ := TS.formCoreSKX p n' W Qq O Kf ι σ j w h m (lamAt lam0 s) (hanti s)
    obtain ⟨β, h1, h2⟩ := posCore_of_formX hinj p m (lamAt lam0 s) _ B ha hb hc hdd
    exact ⟨β, h1, c, hc0, fun Q P => by rw [h2, hcB]⟩
  choose β hβ cs hcs0 hcs using hpos
  have hV : Vsp Kf lam0 = tensorLat Kf Kf
      (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
    unfold Vsp
    congr 1
    funext s
    rw [if_pos (hanti s)]
  obtain ⟨Ψ, hform, hΨ⟩ := ten_sideX O Kf p lam0 hd (fun s => expN p m (lamAt lam0 s)) β hβ cs hcs (Vsp Kf lam0) hV
  have hκ : (p : Kf) ^ ((kap1 p lam0 : ℕ) : ℤ) = (p : Kf) ^ (∑ s, expN p m (lamAt lam0 s)) := by
    rw [zpow_natCast]
    rfl
  refine ⟨Ψ, ∏ s, cs s, Finset.prod_ne_zero_iff.2 (fun s _ => hcs0 s), ?_, hform⟩
  unfold Formalism.MainNotions.TestSideCounting.TSProp
  rw [hκ]
  refine ⟨?_, ?_⟩
  · intro L hL
    obtain ⟨g, hg, rfl⟩ := hL
    have h1 := hΨ (fun s => la_tw ι σ s.val g) (fun s => la_tw_det _ _ _ g hg)
    have e1 : HL (O := O) ι σ lam0 (colSpan W g) =
        (Hten O lam0 fun s => colSpan O (la_tw ι σ s.val g)).comap ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HL toV
      simp only [extO_colSpan h]
    have e2 : HL (O := O) ι σ lam0 (latDual (colSpan W g)) =
        (Hten O lam0 fun s => colSpan O ((la_tw ι σ s.val g)⁻¹).transpose).comap
          ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HL toV
      rw [latDual_colSpan g hg]
      simp only [extO_colSpan h, tw_invT ι σ _ g hg]
    rw [e1, e2]
    exact h1
  · intro e he
    obtain ⟨g, hgb⟩ := edgeBasis h m r e he
    have hg := hgb.1
    have hw := w_ne h
    have hp := p_eq h
    set c : Kf := algebraMap O Kf w with hc
    have hN : ∀ s : Fin n', IsUnit (la_tw ι σ s.val g * lb_D (m + 1) r c).det := by
      intro s
      rw [Matrix.det_mul]
      exact (la_tw_det _ _ _ g hg).mul (lb_D_det _ _ _ hw)
    have h1 := hΨ (fun s => la_tw ι σ s.val g * lb_D (m + 1) r c) hN
    have e1 : HLe (O := O) p ι σ w lam0 e =
        (Hten O lam0 fun s => colSpan O (la_tw ι σ s.val g * lb_D (m + 1) r c)).comap
          ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HLe toV
      simp only [leAt_of_basis h m r e g hgb, ← hc]
    have e2 : HLe (O := O) p ι σ w lam0 e.dual =
        (Hten O lam0 fun s => colSpan O ((la_tw ι σ s.val g * lb_D (m + 1) r c)⁻¹).transpose).comap
          ((Vsp Kf lam0).subtype.restrictScalars O) := by
      unfold HLe toV
      simp only [leAt_of_basis h m r e.dual _ (dual_edgeBasis p r (pQ_ne h) e g hgb), tw_mul, tw_invT ι σ _ g hg,
        tw_dE, invT_mul_D _ (la_tw_det ι σ _ g hg) r c hw, Matrix.mul_assoc, hp, ← hc, dE_sq_D r c hw]
    unfold Re Re'
    rw [e1, e2, scale_map, scale_comm]
    exact ⟨scale_mono _ h1.1, scale_mono _ h1.2⟩

end Formalism.L2.G.Model

namespace Formalism.MainNotions.TestSideCounting

/- English proof (translation)
The claim follows from `Formalism.L2.G.Model.test_side_explicit_identification`.
-/
theorem restTSX : RestTSX := Formalism.L2.G.Model.test_side_explicit_identification

/- English proof (translation)
The claim follows from `restTSOp_of restTSX hOp D CLa Ck Crk Cdeg`.
-/
theorem restTSOp_of_opF (hOp : RestOpF) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestTSOp D CLa Ck Crk Cdeg :=
  restTSOp_of restTSX hOp D CLa Ck Crk Cdeg

end Formalism.MainNotions.TestSideCounting
