import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TypeChainPrincipalEntryNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.TopCongr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Distinguish the cases in `hx : IntM x`. Establish `e : g * x = x + (g - 1) * x` using `by rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]`. Rewrite using `[e, hp x _ hx (hg.mul_intM hx)]`. Take `⟨u, hu, rfl⟩` from `exists_mem_KOne hg`. Establish `h1 : f x = 0` using `by_contra fun h => hx (hs x h)`.

Establish `h2 : f (u.val * x) = 0` using `by_contra fun h => hx (by`. Use `(mem_KO.1 (KOne_le_KO hu)).2.mul (hs _ h)` as an intermediate fact. Rewrite using `[← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this)` and apply the resulting hypothesis. Rewrite using `[h1, h2]`.
-/
theorem mul_invariant {a b : Type} [Fintype a] [DecidableEq a] {f : Matrix a b k → ℂ} (hs : ∀ x, f x ≠ 0 → IntM x)
    (hp : ∀ x y, IntM x → MaxM y → f (x + y) = f x) {g : Matrix a a k} (hg : MaxM (g - 1)) (x : Matrix a b k) :
    f (g * x) = f x := by
  by_cases hx : IntM x
  · have e : g * x = x + (g - 1) * x := by rw [Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
    rw [e, hp x _ hx (hg.mul_intM hx)]
  · obtain ⟨u, hu, rfl⟩ := exists_mem_KOne hg
    have h1 : f x = 0 := by_contra fun h => hx (hs x h)
    have h2 : f (u.val * x) = 0 := by_contra fun h => hx (by
      have := (mem_KO.1 (KOne_le_KO hu)).2.mul (hs _ h)
      rwa [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this)
    rw [h1, h2]

/- English proof (translation)
Use `hν.1` as an intermediate fact. Use `secondCountable k` as an intermediate fact. Establish `hs : ∀ z ∈ box n (1 : kˣ), ∀ x, cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) = cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x` using `fun z hz x => by`. Establish `: (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x` using `(Submodule.Quotient.eq _).2 (by simpa using hz)`. Simplify using `only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]`.

Use `Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1) (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)` and prove the remaining obligations. Simplify using `only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]`. Simplify `h' i trivial` using `[cball, hε, Valuation.mem_integer_iff]`.
-/
theorem hat_eq_zero [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν) {ε : k}
    (hε : valuation k ε = 1) (y₀ : n → k) {η : n → k} (hη : ¬ ∀ i, η i ∈ 𝒪[k]) :
    hat ψ ν ε (cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀)) η = 0 := by
  classical
  have := hν.1
  have := secondCountable k
  have hs : ∀ z ∈ box n (1 : kˣ), ∀ x,
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) (x + z) =
      cosetInd (box n (1 : kˣ)) (Submodule.Quotient.mk y₀) x := fun z hz x => by
    have : (Submodule.Quotient.mk (x + z) : (n → k) ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk x :=
      (Submodule.Quotient.eq _).2 (by simpa using hz)
    simp only [cosetInd, Set.indicator_apply, Set.mem_setOf_eq, this]
  refine Eq.trans ?_ (FourierPi.fourier_eq_zero_pi (Measure.pi fun _ => ν) hψ (s := 1)
    (fun z hz x => hs z (fun i => hz i trivial) x) (y := ε • η) fun h' => hη fun i => ?_)
  · simp only [hat, dotProduct_smul, smul_eq_mul, dotProduct_comm]
  · simpa [cball, hε, Valuation.mem_integer_iff] using h' i trivial

variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

/- English proof (translation)
Establish `e : (typeFrame S.ϖ (stdOrd (Fin κ) t (l` using `s + 1) (s + 1) 0 rfl)).bas = 1 := by`. Express the relevant statement in the definitionally equal form `embA _ _ = 1`. Rewrite using `[Subsingleton.elim (SplitFlip.diagGL _) 1, map_one]`. Express the relevant statement in the definitionally equal form `S.P.iterPhi t S.μ S.tame (s + 1) (LatFrame.coords _ _ z) = _`. Unfold `LatFrame.coords TypeDatum.iterPhi`.

Rewrite using `[e]`. Simplify using `[LatFrame.refl, typeFrame]`.
-/
theorem phiTop_eq (z : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) (XIx (Fin κ) t (s + 1) ⊕ Fin 0) k) :
    (S.T t).PhiTop z = (S.P.iter t S.μ S.tame (s + 1)).Phi t (S.μ (s + 1 + 1))
      (z.submatrix (ixSucc _ t (s + 1)) (stdOrd (Fin κ) t (s + 1) 0 rfl)) := by
  have e : (typeFrame S.ϖ (stdOrd (Fin κ) t (l := s + 1) (s + 1) 0 rfl)).bas = 1 := by
    change embA _ _ = 1
    rw [Subsingleton.elim (SplitFlip.diagGL _) 1, map_one]
  change S.P.iterPhi t S.μ S.tame (s + 1) (LatFrame.coords _ _ z) = _
  unfold LatFrame.coords TypeDatum.iterPhi
  rw [e]
  simp [LatFrame.refl, typeFrame]

/- English proof (translation)
Use `(S.cond 1).2 (by simp) _ ?_` and prove the remaining obligations. Establish `h` using `(S.unif _).1 (hd (Sum.inl (Sum.inr 0)))`. Establish `h0 : (0 : ValueGroupWithZero k) < valuation k (S.ϖ : k)`. Rewrite using `[zero_lt_iff]`. Simplify using the standard rewrite rules.

Simplify using `only [SymData.y0, dotProduct_single, neg_mul, one_mul, Valuation.map_neg, map_mul, map_one, Units.val_inv_eq_inv_val, map_inv₀]`. Rewrite using `[← div_eq_mul_inv]`. Conclude with `(div_le_one₀ h0).2 h`.
-/
theorem symmetricChain_psi_base_eq_one_of_maximalIdeal {d : XIx (Fin κ) t (s + 1) → k} (hd : ∀ i, valuation k (d i) < 1) :
    S.ψ (-1 * (d ⬝ᵥ S.y0 t)) = 1 := by
  refine (S.cond 1).2 (by simp) _ ?_
  have h := (S.unif _).1 (hd (Sum.inl (Sum.inr 0)))
  have h0 : (0 : ValueGroupWithZero k) < valuation k (S.ϖ : k) := by
    rw [zero_lt_iff]; simp
  simp only [SymData.y0, dotProduct_single, neg_mul, one_mul, Valuation.map_neg, map_mul, map_one,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ h0).2 h

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν hν s κ S t _ _ g hg x`. Use `mul_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x` and prove the remaining obligations. Unfold `Chain.xiTop at hx`. Take `⟨h1, h2⟩` from `mul_ne_zero_iff.1 hx`. Introduce and unpack `(i | i) j`.

Rewrite `h1` using `[phiTop_eq]`. Simplify using `using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i) ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))`. Conclude with `by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))`. Unfold `Chain.xiTop`. Establish `hxy` using `hx.add hy.intM`.

Rewrite using `[Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _), phiTop_eq, phiTop_eq]`. Use `congr 1`. Establish `e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0`. Use extensionality with `i (j | j)`. Both sides reduce to the same expression.

Conclude with `j.elim0`. Rewrite using `[e, submatrix_add]`. Use `TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[submatrix_apply]`. Break down `stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j` into its components or cases.

Conclude with `hy _ _`. Conclude with `j.elim0`. Establish `e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ())` using `rfl`. Rewrite using `[e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]`.
-/
theorem xiTop_mul_congr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (g : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) k), (∀ r c, valuation k ((g - 1) r c) < 1) → ∀ x : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2) ⊕ Unit) (XIx (Fin κ) t (s + 1)) k, (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) (g * x) = (S.T t).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 t)) x := by
  intro k _ _ _ _ _ _ ν hν s κ S t _ _ g hg x
  refine mul_invariant (fun x hx => ?_) (fun x y hx hy => ?_) hg x
  · unfold Chain.xiTop at hx
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hx
    rintro (i | i) j
    · rw [phiTop_eq] at h1
      simpa using TypeDatum.intM_of_Phi_ne_zero _ _ h1 ((ixSucc _ t (s + 1)).symm i)
        ((stdOrd (Fin κ) t (s + 1) 0 rfl).symm (Sum.inl j))
    · exact by_contra fun h => h2 (hat_eq_zero S.cond hν (by simp) _ fun h' => h (h' j))
  · unfold Chain.xiTop
    have hxy := hx.add hy.intM
    rw [Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hx _), Model.hat_coset S.cond hν (neg_mem (one_mem _)) _ (hxy _),
      phiTop_eq, phiTop_eq]
    congr 1
    · have e : fromCols (x + y).toRows₁ (0 : Matrix _ (Fin 0) k) = fromCols x.toRows₁ 0 + fromCols y.toRows₁ 0 := by
        ext i (j | j)
        · rfl
        · exact j.elim0
      rw [e, submatrix_add]
      refine TypeDatum.Phi_add _ (S.tame _) _ fun i j => ?_
      rw [submatrix_apply]
      rcases stdOrd (Fin κ) t (s + 1) 0 rfl j with j | j
      · exact hy _ _
      · exact j.elim0
    · have e : (x + y) (Sum.inr ()) = x (Sum.inr ()) + y (Sum.inr ()) := rfl
      rw [e, add_dotProduct, mul_add, AddChar.map_add_eq_mul, symmetricChain_psi_base_eq_one_of_maximalIdeal S t (hy _), mul_one]

end GlobalTheory.TopCongr
