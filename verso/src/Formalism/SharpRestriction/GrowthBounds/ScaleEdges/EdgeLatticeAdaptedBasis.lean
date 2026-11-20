import Formalism.LocalToGlobal.GroupLattices.FockModels.ElementaryDivisorBasis
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.ScaleNegMono

open MvPolynomial

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.G.LatticeSystems Formalism.L2.G.Model

def ordMax {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℤ :=
  ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r, (lamAt lam0 s a - lamAt lam0 s (Fin.last m))

/- English proof (translation)
Take `⟨b, hb, hbd⟩` from `Formalism.MainNotions.G.LatticeSystems.lb_basis O (m + 1) (m + 1) (nuOf lam)`. Take `⟨hKi, hKs⟩` from `nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg`. Establish `hdet0 : g.det ≠ 0` using `hg.ne_zero`. Use `set ll := lam (Fin.last m) with hll`. Use `set S := Finset.univ.filter fun a : Fin (m + 1) => a.val < r with hS`.

Use `set f := fun i : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hf`. Establish `hdg0 : g.det ^ (-ll) ≠ 0` using `zpow_ne_zero _ hdet0`. Use `⟨fun i => g.det ^ (-ll) • f i, fun i => ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) + (S.card : ℤ) * ll, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hKi.units_smul (fun _ => Units.mk0 (g.det ^ (-ll)) hdg0)`. Rewrite using `[← Set.smul_set_range, Submodule.span_smul_eq_of_isUnit _ _ (Ne.isUnit hdg0)]`.

Conclude with `hKs`. Introduce `i`. Establish `h1` using `hbd i r`. Establish `h2 : ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ∑ a ∈ S, (lam a - ll)`. Combine the equalities or inequalities in the displayed calculation.

Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `: ll ≤ lam a` using `hlam (Fin.le_last a)`. Simplify using `only [nuOf]`. Use linear arithmetic over natural numbers and integers.

Establish `h3 : ∑ a ∈ S, (lam a - ll) = ∑ a ∈ S, lam a - (S.card : ℤ) * ll`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`. Establish `: (0 : ℤ) ≤ ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ)` using `Int.natCast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `c hc`. Establish `ht : ∀ a : Fin (m + 1), (if a.val < r then c⁻¹ else 1) ≠ 0`. Apply the tactic sequence `intro a; split_ifs <;> simp [hc]`. Take `⟨-, hD⟩` from `nablaLDiag O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g _ hg ht`.

Establish `hgD : g * lb_D (m + 1) r c = g * Matrix.diagonal (fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1)` using `rfl`. Rewrite using `[nablaLTw, hgD]`. Express the relevant statement in the definitionally equal form `_ = Submodule.map _ (nablaL O Kf (m + 1) (m + 1) (nuOf lam) _)`. Rewrite using `[← hD, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`.

Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp]`. Establish `hprod : (∏ a, (if a.val < r then c⁻¹ else 1) ^ rowWt i.1 a)⁻¹ = c ^ (∑ a ∈ S, rowWt i.1 a)`. Repeatedly rewrite using `[ite_pow, one_pow]`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum, inv_pow, inv_inv]`.

Establish `hdet : (g * Matrix.diagonal fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1).det = g.det * c⁻¹ ^ S.card`. Rewrite using `[Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]`. Establish `hpw : (c⁻¹ ^ S.card) ^ (-ll) = c ^ ((S.card : ℤ) * ll)`. Rewrite using `[inv_pow, inv_zpow', ← zpow_natCast, ← zpow_mul]`. Put the polynomial expressions in normal form.

Rewrite using `[hdet, ← hll, hprod]`. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]`. Use `congr 1`. Rewrite using `[mul_zpow, hpw, zpow_add₀ hc, zpow_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pos_basisO (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf]
    (hinj : Function.Injective (algebraMap O Kf)) (m r : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hg : IsUnit g.det) :
    ∃ (X : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf)
      (π : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) → ℤ),
      LinearIndependent Kf X ∧ Submodule.span Kf (Set.range X) = dualWeyl Kf (m + 1) (m + 1) (nuOf lam) ∧
      (∀ i, π i ≤ ∑ a : Fin (m + 1) with a.val < r, lam a) ∧
      (∀ i, ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * lam (Fin.last m) ≤ π i) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • X i) =
        nablaLTw O Kf m lam (g * lb_D (m + 1) r c) := by
  classical
  obtain ⟨b, hb, hbd⟩ := Formalism.MainNotions.G.LatticeSystems.lb_basis O (m + 1) (m + 1) (nuOf lam)
  obtain ⟨hKi, hKs⟩ := nablaLKBasis O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g hg
  have hdet0 : g.det ≠ 0 := hg.ne_zero
  set ll := lam (Fin.last m) with hll
  set S := Finset.univ.filter fun a : Fin (m + 1) => a.val < r with hS
  set f := fun i : ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) => rowAct Kf g⁻¹ (map (algebraMap O Kf) (b i)) with hf
  have hdg0 : g.det ^ (-ll) ≠ 0 := zpow_ne_zero _ hdet0
  refine ⟨fun i => g.det ^ (-ll) • f i,
    fun i => ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) + (S.card : ℤ) * ll, ?_, ?_, ?_, ?_, ?_⟩
  · exact hKi.units_smul (fun _ => Units.mk0 (g.det ^ (-ll)) hdg0)
  · rw [← Set.smul_set_range, Submodule.span_smul_eq_of_isUnit _ _ (Ne.isUnit hdg0)]
    exact hKs
  · intro i
    have h1 := hbd i r
    have h2 : ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ∑ a ∈ S, (lam a - ll) := by
      calc ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) ≤ ((∑ a ∈ S, nuOf lam a : ℕ) : ℤ) := by exact_mod_cast h1
        _ = ∑ a ∈ S, (lam a - ll) := by
          push_cast
          refine Finset.sum_congr rfl fun a _ => ?_
          have : ll ≤ lam a := hlam (Fin.le_last a)
          simp only [nuOf]
          omega
    have h3 : ∑ a ∈ S, (lam a - ll) = ∑ a ∈ S, lam a - (S.card : ℤ) * ll := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith
  · intro i
    have : (0 : ℤ) ≤ ((∑ a ∈ S, rowWt i.1 a : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  · intro c hc
    have ht : ∀ a : Fin (m + 1), (if a.val < r then c⁻¹ else 1) ≠ 0 := by
      intro a; split_ifs <;> simp [hc]
    obtain ⟨-, hD⟩ := nablaLDiag O Kf hinj (m + 1) (m + 1) (nuOf lam) b _ hb g _ hg ht
    have hgD : g * lb_D (m + 1) r c =
        g * Matrix.diagonal (fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1) := rfl
    rw [nablaLTw, hgD]
    change _ = Submodule.map _ (nablaL O Kf (m + 1) (m + 1) (nuOf lam) _)
    rw [← hD, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp]
    have hprod : (∏ a, (if a.val < r then c⁻¹ else 1) ^ rowWt i.1 a)⁻¹ = c ^ (∑ a ∈ S, rowWt i.1 a) := by
      simp_rw [ite_pow, one_pow]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_pow_eq_pow_sum, inv_pow, inv_inv]
    have hdet : (g * Matrix.diagonal fun a : Fin (m + 1) => if a.val < r then c⁻¹ else 1).det =
        g.det * c⁻¹ ^ S.card := by
      rw [Matrix.det_mul, Matrix.det_diagonal, Finset.prod_ite, Finset.prod_const_one, mul_one,
        Finset.prod_const]
    have hpw : (c⁻¹ ^ S.card) ^ (-ll) = c ^ ((S.card : ℤ) * ll) := by
      rw [inv_pow, inv_zpow', ← zpow_natCast, ← zpow_mul]
      ring_nf
    rw [hdet, ← hll, hprod]
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, smul_smul]
    congr 1
    rw [mul_zpow, hpw, zpow_add₀ hc, zpow_natCast]
    ring

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O Kf)` using `IsFractionRing.injective O Kf`. Establish `hinj' : Function.Injective fun a : O => a • (1 : Kf)`. Establish `: (fun a : O => a • (1 : Kf)) = algebraMap O Kf`. Use function extensionality and compare the values at `fun a => (Algebra.algebraMap_eq_smul_one a).symm`. Rewrite using `[this]`.

Conclude with `hinj`. Establish `hA : ∀ s, Antitone (lamAt lam0 s)` using `kp_lamAt_antitone lam0 hd`. Establish `hI` using `Formalism.MainNotions.G.LatticeSystems.la_indep (O := O) (Kf := Kf) hinj`. Establish `hpos` using `fun s => pos_basisO O Kf hinj m r (lamAt lam0 s) (hA s) (gs s) (hgs s)`. Use `choose X π hXi hXs hup hlo hspan using hpos`.

Establish `: ∀ s, Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))` using `fun s => (sSIdxFinite _ _ _).to_subtype`. Establish `: ∀ s, Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))` using `fun s => Fintype.ofFinite _`. Establish `: IsFractionRing Kf Kf` using `jr_KK Kf`. Use `set P : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) → MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf := fun i => ∏ s, blockEmb Kf s (X s (i s)) with hP`. Take `⟨hPi, hPs⟩` from `tensorBasis Kf Kf (Fin n') (m + 1) (m + 1) _ _ X hXi hXs`.

Establish `hV : Vsp Kf lam0 = Submodule.span Kf (Set.range P)`. Rewrite using `[hPs]`. Simplify using `only [Vsp, hA, ↓reduceIte]`. Establish `hmem : ∀ i, P i ∈ Vsp Kf lam0` using `fun i => hV ▸ Submodule.subset_span ⟨i, rfl⟩`. Use `set y : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) → Vsp Kf lam0 := fun i => ⟨P i, hmem i⟩ with hy`.

Establish `hyi : LinearIndependent Kf y` using `LinearIndependent.of_comp (Vsp Kf lam0).subtype hPi`. Establish `hys : Submodule.span Kf (Set.range y) = ⊤`. Rewrite using `[eq_top_iff, ← comap_span_coe (O := Kf) (Kf := Kf) (Vsp Kf lam0) y]`. Introduce `v _`. Rewrite using `[Submodule.mem_comap]`.

Establish `hv : (v : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Submodule.span Kf (Set.range P)` using `hV ▸ v.2`. Conclude with `hv`. Use `⟨_, inferInstance, Module.Basis.mk hyi hys.symm.le, fun i => ∑ s, π s (i s), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Unfold `Ar`.

Conclude with `Finset.sum_le_sum fun s _ => hup s (i s)`. Introduce `i`. Unfold `Ar ordMax`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_le_sum fun s _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]`. Combine the linear relations using `[hlo s (i s)]`. Introduce `c hc`. Establish `hdet : ∀ s, IsUnit (gs s * lb_D (m + 1) r c).det` using `fun s => by`. Rewrite using `[Matrix.det_mul]`.

Conclude with `(hgs s).mul (lb_D_det _ _ _ hc)`. Establish `hli : ∀ s, LinearIndependent O fun j => c ^ π s j • X s j` using `fun s => ((hXi s).units_smul fun j => Units.mk0 (c ^ π s j) (zpow_ne_zero _ hc)).restrict_scalars hinj'`. Take `⟨-, hT⟩` from `tensorBasis O Kf (Fin n') (m + 1) (m + 1) _ (fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j)) (fun s j => c ^ π s j • X s j) hli (fun s => rfl)`. Establish `hH : Hten O lam0 (fun s => colSpan O (gs s * lb_D (m + 1) r c)) = Submodule.span O (Set.range fun i => c ^ (∑ s, π s (i s)) • P i)`. Establish `e1 : (fun s => H0 O m (lamAt lam0 s) (colSpan O (gs s * lb_D (m + 1) r c))) = fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j)`.

Use function extensionality and compare the values at `s`. Rewrite using `[H0_eq_twisted_nabla hI m _ (hA s) _ (hdet s), hspan s c hc]`. Rewrite using `[Hten, e1, ← hT]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using `only [hP, MvPolynomial.smul_eq_C_mul, map_mul, blockEmb, MvPolynomial.rename_C, Finset.prod_mul_distrib]`. Rewrite using `[← map_prod, lb_zpow_sum c hc]`. Rewrite using `[toV, hH, ← comap_span_coe (O := O) (Kf := Kf) (Vsp Kf lam0) (fun i => c ^ (∑ s, π s (i s)) • (Module.Basis.mk hyi hys.symm.le) i)]`. Use `congr 3`. Use function extensionality and compare the values at `i`.

Rewrite using `[Submodule.coe_smul, Module.Basis.mk_apply]`.
-/
theorem ten_basisO (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf]
    {n' m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam0)
    (gs : Fin n' → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hgs : ∀ s, IsUnit (gs s).det) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf (Vsp Kf lam0)) (π : I → ℤ),
      (∀ i, π i ≤ Ar r lam0) ∧ (∀ i, Ar r lam0 - π i ≤ ordMax r lam0) ∧
      ∀ c : Kf, c ≠ 0 → Submodule.span O (Set.range fun i => c ^ π i • x i) =
        toV lam0 (Hten O lam0 fun s => colSpan O (gs s * lb_D (m + 1) r c)) := by
  classical
  have hinj : Function.Injective (algebraMap O Kf) := IsFractionRing.injective O Kf
  have hinj' : Function.Injective fun a : O => a • (1 : Kf) := by
    have : (fun a : O => a • (1 : Kf)) = algebraMap O Kf :=
      funext fun a => (Algebra.algebraMap_eq_smul_one a).symm
    rw [this]; exact hinj
  have hA : ∀ s, Antitone (lamAt lam0 s) := kp_lamAt_antitone lam0 hd
  have hI := Formalism.MainNotions.G.LatticeSystems.la_indep (O := O) (Kf := Kf) hinj
  have hpos := fun s => pos_basisO O Kf hinj m r (lamAt lam0 s) (hA s) (gs s) (hgs s)
  choose X π hXi hXs hup hlo hspan using hpos
  have : ∀ s, Finite ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) :=
    fun s => (sSIdxFinite _ _ _).to_subtype
  have : ∀ s, Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := fun s => Fintype.ofFinite _
  have : IsFractionRing Kf Kf := jr_KK Kf
  set P : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) →
      MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf :=
    fun i => ∏ s, blockEmb Kf s (X s (i s)) with hP
  obtain ⟨hPi, hPs⟩ := tensorBasis Kf Kf (Fin n') (m + 1) (m + 1) _ _ X hXi hXs
  have hV : Vsp Kf lam0 = Submodule.span Kf (Set.range P) := by
    rw [hPs]
    simp only [Vsp, hA, ↓reduceIte]
  have hmem : ∀ i, P i ∈ Vsp Kf lam0 := fun i => hV ▸ Submodule.subset_span ⟨i, rfl⟩
  set y : (∀ s : Fin n', ↥(ssIdx (m + 1) (m + 1) (nuOf (lamAt lam0 s)))) → Vsp Kf lam0 :=
    fun i => ⟨P i, hmem i⟩ with hy
  have hyi : LinearIndependent Kf y := LinearIndependent.of_comp (Vsp Kf lam0).subtype hPi
  have hys : Submodule.span Kf (Set.range y) = ⊤ := by
    rw [eq_top_iff, ← comap_span_coe (O := Kf) (Kf := Kf) (Vsp Kf lam0) y]
    intro v _
    rw [Submodule.mem_comap]
    have hv : (v : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ Submodule.span Kf (Set.range P) :=
      hV ▸ v.2
    exact hv
  refine ⟨_, inferInstance, Module.Basis.mk hyi hys.symm.le, fun i => ∑ s, π s (i s), ?_, ?_, ?_⟩
  · intro i
    unfold Ar
    exact Finset.sum_le_sum fun s _ => hup s (i s)
  · intro i
    unfold Ar ordMax
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    linarith [hlo s (i s)]
  · intro c hc
    have hdet : ∀ s, IsUnit (gs s * lb_D (m + 1) r c).det := fun s => by
      rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hc)
    have hli : ∀ s, LinearIndependent O fun j => c ^ π s j • X s j := fun s =>
      ((hXi s).units_smul fun j => Units.mk0 (c ^ π s j) (zpow_ne_zero _ hc)).restrict_scalars hinj'
    obtain ⟨-, hT⟩ := tensorBasis O Kf (Fin n') (m + 1) (m + 1) _
      (fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j)) (fun s j => c ^ π s j • X s j)
      hli (fun s => rfl)
    have hH : Hten O lam0 (fun s => colSpan O (gs s * lb_D (m + 1) r c)) =
        Submodule.span O (Set.range fun i => c ^ (∑ s, π s (i s)) • P i) := by
      have e1 : (fun s => H0 O m (lamAt lam0 s) (colSpan O (gs s * lb_D (m + 1) r c))) =
          fun s => Submodule.span O (Set.range fun j => c ^ π s j • X s j) := by
        funext s
        rw [H0_eq_twisted_nabla hI m _ (hA s) _ (hdet s), hspan s c hc]
      rw [Hten, e1, ← hT]
      congr 2
      funext i
      simp only [hP, MvPolynomial.smul_eq_C_mul, map_mul, blockEmb, MvPolynomial.rename_C,
        Finset.prod_mul_distrib]
      rw [← map_prod, lb_zpow_sum c hc]
    rw [toV, hH, ← comap_span_coe (O := O) (Kf := Kf) (Vsp Kf lam0)
      (fun i => c ^ (∑ s, π s (i s)) • (Module.Basis.mk hyi hys.symm.le) i)]
    congr 3
    funext i
    rw [Submodule.coe_smul, Module.Basis.mk_apply]

section
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

/- English proof (translation)
Establish `hw` using `w_ne h`. Establish `hp` using `p_eq h`. Establish `hp0 : (p : Kf) ≠ 0` using `by rw [hp]; exact pow_ne_zero 2 hw`. Establish `: IsFractionRing O Kf` using `h.frac_O`. Take `⟨gs, hgs, hsrc, hLe, htgt⟩` from `edgeLat h m r e he`.

Take `⟨I, hI, x, π, hup, hord, hsp⟩` from `ten_basisO O Kf r lam0 hd (fun s : Fin n' => gs s.val) (fun s => hgs s.val)`. Establish `h3 : Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e`. Rewrite using `[HLe, show (fun s : Fin n' => LeAt p ι σ w s.val e) = fun s => colSpan O (gs s.val * lb_D (m + 1) r (algebraMap O Kf w)) from funext fun s => hLe s.val]`. Conclude with `hsp _ hw`. Use `⟨I, hI, x, π, ?_, ?_, h3, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[HL, show (fun s : Fin n' => extO O ι σ s.val e.src) = fun s => colSpan O (gs s.val) from`. Use function extensionality and compare the values at `fun s => hsrc s.val]`. Simplify `hsp 1 one_ne_zero` using `[lb_D_one]`. Rewrite using `[HL, show (fun s : Fin n' => extO O ι σ s.val e.tgt) = fun s => colSpan O (gs s.val * lb_D (m + 1) r (p : Kf)) from`. Use function extensionality and compare the values at `fun s => by rw [htgt, Matrix.mul_assoc, lb_D_sq, hp]]`.

Conclude with `hsp _ hp0`. Introduce `i`. Unfold `order`. Combine the linear relations using `[hup i]`. Conclude with `hord`.

Rewrite using `[Re, ← h3, scale_span]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[smul_smul, order, ← zpow_add₀ hw]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Re', ← h3, dualLat_span x _ (fun i => zpow_ne_zero _ hw), scale_span]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Rewrite using `[smul_smul]`.

Use `congr 1`. Rewrite using `[hp, order, ← zpow_neg, ← zpow_natCast (algebraMap O Kf w) 2, ← zpow_mul, ← zpow_add₀ hw, ← zpow_add₀ hw]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem edge_lattice_adapted_basis (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) :
    ∃ (I : Type) (_ : Finite I) (x : Module.Basis I Kf ↥(Vsp Kf lam0)) (π : I → ℤ),
      Submodule.span O (Set.range x) = HL ι σ lam0 e.src ∧
      Submodule.span O (Set.range fun i => ((p : Kf) ^ π i) • x i) = HL ι σ lam0 e.tgt ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e ∧
      (∀ i, 0 ≤ order r lam0 (π i)) ∧ (∀ i, order r lam0 (π i) ≤ ordMax r lam0) ∧
      Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i) =
        Re p ι σ w r lam0 e ∧
      Submodule.span O (Set.range fun i =>
          (algebraMap O Kf w ^ (-order r lam0 (π i)) * (p : Kf) ^ (-π i)) • x.coord i) =
        Re' p ι σ w r lam0 e := by
  classical
  have hw := w_ne h
  have hp := p_eq h
  have hp0 : (p : Kf) ≠ 0 := by rw [hp]; exact pow_ne_zero 2 hw
  have : IsFractionRing O Kf := h.frac_O
  obtain ⟨gs, hgs, hsrc, hLe, htgt⟩ := edgeLat h m r e he
  obtain ⟨I, hI, x, π, hup, hord, hsp⟩ :=
    ten_basisO O Kf r lam0 hd (fun s : Fin n' => gs s.val) (fun s => hgs s.val)
  have h3 : Submodule.span O (Set.range fun i => (algebraMap O Kf w ^ π i) • x i) = HLe p ι σ w lam0 e := by
    rw [HLe, show (fun s : Fin n' => LeAt p ι σ w s.val e) =
      fun s => colSpan O (gs s.val * lb_D (m + 1) r (algebraMap O Kf w)) from funext fun s => hLe s.val]
    exact hsp _ hw
  refine ⟨I, hI, x, π, ?_, ?_, h3, ?_, ?_, ?_, ?_⟩
  · rw [HL, show (fun s : Fin n' => extO O ι σ s.val e.src) = fun s => colSpan O (gs s.val) from
      funext fun s => hsrc s.val]
    simpa [lb_D_one] using hsp 1 one_ne_zero
  · rw [HL, show (fun s : Fin n' => extO O ι σ s.val e.tgt) =
      fun s => colSpan O (gs s.val * lb_D (m + 1) r (p : Kf)) from
      funext fun s => by rw [htgt, Matrix.mul_assoc, lb_D_sq, hp]]
    exact hsp _ hp0
  · intro i
    unfold order
    linarith [hup i]
  · exact hord
  · rw [Re, ← h3, scale_span]
    congr 2
    funext i
    rw [smul_smul, order, ← zpow_add₀ hw]
    congr 2
    ring
  · rw [Re', ← h3, dualLat_span x _ (fun i => zpow_ne_zero _ hw), scale_span]
    congr 2
    funext i
    rw [smul_smul]
    congr 1
    rw [hp, order, ← zpow_neg, ← zpow_natCast (algebraMap O Kf w) 2, ← zpow_mul, ← zpow_add₀ hw,
      ← zpow_add₀ hw]
    congr 1
    push_cast
    ring

/- English proof (translation)
Take `⟨I, hI, x, π, hsrc, -, -, -, hmax, hRe, -⟩` from `edge_lattice_adapted_basis h m r lam0 hd e he`. Establish `hw` using `w_ne h`. Rewrite using `[← hRe, ← hsrc, scale_span, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Establish `hk : 0 ≤ (M : ℤ) - order r lam0 (π i)` using `by linarith [hmax i]`.

Take `⟨k, hk'⟩` from `Int.eq_ofNat_of_zero_le hk`. Establish `he' : (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i = (w ^ k) • ((algebraMap O Kf w ^ (-(M : ℤ))) • x i)`. Rewrite using `[← algebraMap_smul Kf (w ^ k), smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]`. Use `congr 2`. Use linear arithmetic over natural numbers and integers.

Use `beta_reduce`. Rewrite using `[SetLike.mem_coe, he']`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem Re_le_scale_HL (h : HidaSetting p n' W Qq O Kf ι σ j w) (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (hd : IsDominant lam0) (e : Edge W Qq (m + 1)) (he : IsEdge p n' r e) (M : ℕ) (hM : ordMax r lam0 ≤ M) :
    Re p ι σ w r lam0 e ≤ scale (algebraMap O Kf w ^ (-(M : ℤ))) (HL (O := O) ι σ lam0 e.src) := by
  obtain ⟨I, hI, x, π, hsrc, -, -, -, hmax, hRe, -⟩ := edge_lattice_adapted_basis h m r lam0 hd e he
  have hw := w_ne h
  rw [← hRe, ← hsrc, scale_span, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hk : 0 ≤ (M : ℤ) - order r lam0 (π i) := by linarith [hmax i]
  obtain ⟨k, hk'⟩ := Int.eq_ofNat_of_zero_le hk
  have he' : (algebraMap O Kf w ^ (-order r lam0 (π i))) • x i =
      (w ^ k) • ((algebraMap O Kf w ^ (-(M : ℤ))) • x i) := by
    rw [← algebraMap_smul Kf (w ^ k), smul_smul, map_pow, ← zpow_natCast, ← zpow_add₀ hw]
    congr 2
    omega
  beta_reduce
  rw [SetLike.mem_coe, he']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end

end Formalism.MainNotions.Pf14
