import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralOfCountableCommutatorsUnitary
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead

variable {D : D7}

/- English proof (translation)
Simplify using `only [archM, map_mul, Units.val_mul, Matrix.map_mul]`.
-/
theorem archM_mul' (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    archM V th (g * g') = archM V th g * archM V th g' := by
  simp only [archM, map_mul, Units.val_mul, Matrix.map_mul]

/- English proof (translation)
Simplify using `only [archM, map_one, Units.val_one]`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem archM_one' (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) :
    archM V th 1 = 1 := by
  simp only [archM, map_one, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_right_inverse (B := archM V th g⁻¹) (by rw [← archM_mul', mul_inv_cancel, archM_one'])`.
-/
theorem archM_det_unit (V : HSp D) (th : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g : GA D V) :
    IsUnit (archM V th g).det :=
  Matrix.isUnit_det_of_right_inverse (B := archM V th g⁻¹) (by rw [← archM_mul', mul_inv_cancel, archM_one'])

/- English proof (translation)
Take `⟨δ₀, -, he⟩` from `hδ`. Establish `he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j` using `fun i j => (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm`. Use `⟨δ₀, fun τ θ hθ => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _`.

Rewrite using `[he', Algebra.TensorProduct.map_tmul, map_one]`. Conclude with `hθ.1 _`.
-/
theorem archM_rational (V : HSp D) (δ : GA D V) (hδ : δ ∈ GQ V) :
    ∃ δ₀ : GL (Fin V.rank) D.host.E,
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), IsInfEmb τ θ →
        archM V θ δ = δ₀.1.map τ := by
  obtain ⟨δ₀, -, he⟩ := hδ
  have he' : ∀ i j, (matHom V δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  refine ⟨δ₀, fun τ θ hθ => ?_⟩
  ext i j
  change θ (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V δ).1 i j)) = _
  rw [he', Algebra.TensorProduct.map_tmul, map_one]
  exact hθ.1 _

/- English proof (translation)
Establish `h1 : Xᴴ = J * (-X) * J⁻¹`. Rewrite using `[mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]`. Express the relevant statement in the definitionally equal form `(NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J`. Rewrite using `[← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ), nonsing_inv_mul_cancel_right _ _ hJ, Matrix.mul_assoc, ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]`.
-/
theorem exp_unitary_of_lie {n : ℕ} {J X : Matrix (Fin n) (Fin n) ℂ} (hJ : IsUnit J.det) (hX : Xᴴ * J + J * X = 0) :
    NormedSpace.exp X ∈ Formalism.QuantumDeterminants.UH J := by
  have h1 : Xᴴ = J * (-X) * J⁻¹ := by
    rw [mul_neg, ← eq_neg_of_add_eq_zero_left hX, mul_nonsing_inv_cancel_right _ _ hJ]
  change (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ ((isUnit_iff_isUnit_det J).2 hJ),
    nonsing_inv_mul_cancel_right _ _ hJ, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_left, neg_add_cancel, NormedSpace.exp_zero, Matrix.mul_one]

/- English proof (translation)
Introduce `ρ`. Establish `h` using `hO _ (hΨ ρ)`. Establish `hG : X.Gm = -V.gram.transpose`. Rewrite using `[hW.1]`. Both sides reduce to the same expression.

Use extensionality with `b a`. Establish `h1` using `congrFun (congrFun h a) b`. Establish `h2 : ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a = -ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) X.Gm (x₀ (tauE D ρ)) a b`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, hG, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, gramAt, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, map_neg, Finset.sum_mul, ← Finset.sum_neg …`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `show ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a = _`. Rewrite using `[h2, h1]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Simplify using `only [Matrix.diagonal_apply_eq, sgn]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]`.
-/
theorem negFirst_of_orth (V : HSp D) (X : Data D.host.E V.rank) (hW : ModelW V rfl X)
    (hΨ : ∀ ρ, tauE D ρ ∈ X.Ψ) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hO : IsOrthogonalFrame X x₀) :
    NegFirst V X.p0 fun ρ => x₀ (tauE D ρ) := by
  intro ρ
  have h := hO _ (hΨ ρ)
  have hG : X.Gm = -V.gram.transpose := by
    rw [hW.1]; rfl
  ext b a
  have h1 := congrFun (congrFun h a) b
  have h2 : ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a =
      -ReciprocityTheory.ChartRestriction.G.FD.gram (tauE D ρ) X.Gm (x₀ (tauE D ρ)) a b := by
    simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, hG, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      gramAt, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, map_neg, Finset.sum_mul,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [starRingEnd_apply]
    ring
  show ((x₀ (tauE D ρ))ᴴ * gramAt D V ρ * x₀ (tauE D ρ)) b a = _
  rw [h2, h1]
  by_cases hab : a = b
  · subst hab
    simp only [Matrix.diagonal_apply_eq, sgn]
    split_ifs <;> simp
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ (Ne.symm hab), neg_zero]

/- English proof (translation)
Establish `h1` using `congrArg Matrix.det (h ρ)`. Rewrite `h1` using `[Matrix.det_mul, Matrix.det_diagonal]`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Rewrite `h1` using `[h0, mul_zero]`.

Use `(Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem NegFirst.det_unit {V : HSp D} {q : ℕ} {x : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (h : NegFirst V q x) (ρ : D.what₂.Tau) : IsUnit (x ρ).det := by
  have h1 := congrArg Matrix.det (h ρ)
  rw [Matrix.det_mul, Matrix.det_diagonal] at h1
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, mul_zero] at h1
  refine (Finset.prod_ne_zero_iff.2 fun c _ => ?_) h1.symm
  split_ifs <;> simp

/- English proof (translation)
Substitute `hr` using the available equality. Establish `hre : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ, Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) M = M` using `fun M => rfl`. Take `⟨-, -, ⟨x0, hx0, hmul⟩, -, -, hfib⟩` from `hD`. Establish `e1 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th k τ = θ ρ` using `fun k τ ρ e => GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth k τ) (e ▸ hθ ρ)`. Establish `e2 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th' k τ = θ ρ` using `fun k τ ρ e => GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth' k τ) (e ▸ hθ ρ)`.

Establish `hN : ∀ k, NegFirst V (X k).p0 fun ρ => x₀ (tauE D ρ)` using `fun k => negFirst_of_orth V (X k) (hW k) (fun ρ => (hΨ k _).2 ⟨ρ, rfl⟩) x₀ (hO k)`. Establish `hL' : ∀ h k (y : Frame (X k).Ψ V.rank), dict h = ⟨k, y⟩ → ∃ γ ∈ GQ V, ∀ ρ (τ : (X k).Ψ), τ.1 = tauE D ρ → mat y τ = archM V (θ ρ) (γ * h) * x₀ (tauE D ρ)`. Introduce `h k y e`. Use `hL h` as an intermediate fact. Rewrite `this` using `[e]`.

Take `⟨γ, hγ, H⟩` from `this`. Use `⟨γ, hγ, fun ρ τ eτ => ?_⟩` and prove the remaining obligations. Use `H τ` as an intermediate fact. Rewrite `this` using `[hre, e2 k τ ρ eτ, eτ]`. Conclude with `this`.

Establish `hmul' : ∀ g k (y : Frame (X k).Ψ V.rank), dict g = ⟨k, y⟩ → ∀ u ∈ GinfC V, ∃ γ' ∈ (X k).Γ, dict (g * u) = ⟨k, lact γ' (rmul y (archMat V th rfl x0 u k))⟩`. Introduce `g k y e u hu`. Use `hmul g u hu` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`.

Establish `hA : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ = (mat (x0 k) τ)⁻¹ * archM V (θ ρ) u * mat (x0 k) τ`. Introduce `k τ ρ e u`. Rewrite using `[← e1 k τ ρ e]`. Both sides reduce to the same expression. Establish `hcen : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ = (x₀ (tauE D ρ))⁻¹ * archM V (θ ρ) u * x₀ (tauE D ρ)`.

Introduce `k τ ρ e`. Take `⟨g0, hg0⟩` from `(hx0 k).2`. Take `⟨γ0, hγ0, H0⟩` from `hL' g0 k _ hg0`. Establish `H0'` using `H0 ρ τ e`. Use `set a := archM V (θ ρ) (γ0 * g0) with ha`.

Use `set x := x₀ (tauE D ρ) with hx`. Establish `hxu : IsUnit x.det` using `(hN k).det_unit ρ`. Establish `hau : IsUnit a.det` using `archM_det_unit _ _ _`. Establish `haxu : IsUnit (a * x).det` using `by rw [Matrix.det_mul]; exact hau.mul hxu`. Use `haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable`.

Use `haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) := inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))`. Establish `hc : ∀ w, w * a = a * w`. Use `GlobalTheory.central_of_countable_commutators_unitary V.rank (gramAt D V ρ) a (Set.range fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (tauE D ρ)) (GlobalTheory.SmoothForms.RealPts.gramAt_herm V ρ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) hau (Set.countable …` and prove the remaining obligations. Establish `hZ' : Zᴴ * gramAt D V ρ + gramAt D V ρ * Z = 0` using `hZ`. Establish `hU : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ)`.

Use `exp_unitary_of_lie (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) ?_` and prove the remaining obligations. Rewrite using `[Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ', smul_zero]`. Take `⟨u, hu, huU⟩` from `(GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 (fun ρ' => if ρ' = ρ then NormedSpace.exp (t • Z) else 1) (fun ρ' => by`. Distinguish the cases in `h : ρ' = ρ`. Substitute `h` using the available equality.

Simplify using `using hU`. Simplify using `[h, Formalism.QuantumDeterminants.UH])`. Establish `hUu : archM V (θ ρ) u = NormedSpace.exp (t • Z)`. Use `huU ρ` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`.

Conclude with `this`. Establish `hinv : NormedSpace.exp (t • Z) * NormedSpace.exp (-(t • Z)) = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]`. Simplify using the standard rewrite rules. Generalize the expression as in `NormedSpace.exp (t • Z) = U at hUu hinv`.

Generalize the expression as in `NormedSpace.exp (-(t • Z)) = U' at hinv`. Take `⟨γ', -, h1⟩` from `hmul' g0 k _ hg0 u hu`. Take `⟨γ'', hγ'', h2⟩` from `hL' _ k _ h1`. Establish `h3` using `h2 ρ τ e`. Take `⟨δ, hδ⟩` from `archM_rational V (γ'' * γ0⁻¹) (mul_mem hγ'' (inv_mem hγ0))`.

Establish `h4 : γ'' * (g0 * u) = (γ'' * γ0⁻¹) * (γ0 * g0) * u` using `by group`. Rewrite `h3` using `[h4, archM_mul', archM_mul', hδ _ _ (hθ ρ), ← ha, hUu]`. Express the relevant statement in the definitionally equal form `γ'.1.map τ.1 * (mat (x0 k) τ * mat (archMat V th rfl x0 u k) τ) = _ at h3`. Rewrite `h3` using `[hA k τ ρ e, H0', hUu, e, ← Matrix.mul_assoc (a * x), ← Matrix.mul_assoc (a * x), Matrix.mul_nonsing_inv _ haxu, Matrix.one_mul, ← hx]`. Establish `h5 : γ'.1.map (tauE D ρ) * (U * a) = δ.1.map (tauE D ρ) * a * U`.

Use `congrArg (· * x⁻¹) h3` as an intermediate fact. Simplify `this` using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hxu, Matrix.mul_one]`. Use `⟨(γ'⁻¹).1 * δ.1, ?_⟩` and prove the remaining obligations. Establish `h6 : (γ'⁻¹).1.map (tauE D ρ) * γ'.1.map (tauE D ρ) = 1`. Rewrite using `[← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Use `show ((γ'⁻¹).1 * δ.1).map (tauE D ρ) = _`. Rewrite using `[Matrix.map_mul, ← Matrix.one_mul (U * a), ← h6, Matrix.mul_assoc _ _ (U * a), h5]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc U, hinv, Matrix.one_mul, Matrix.mul_nonsing_inv _ hau, Matrix.mul_one]`. Introduce `u`.

Rewrite using `[hA k τ ρ e, H0', Matrix.mul_inv_rev, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc a⁻¹, ← Matrix.mul_assoc _ a, hc, Matrix.mul_assoc a, ← Matrix.mul_assoc a⁻¹, Matrix.nonsing_inv_mul _ hau, Matrix.one_mul]`. Use `⟨fun ρ => x₀ (tauE D ρ), fun k => ⟨⟨hΨ k, hW k⟩, hN k, ?_⟩, fun h => ?_, hfib⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `(hx0 k).2`. Conclude with `⟨g, by rw [hg]⟩`. Take `⟨γ, hγ, H⟩` from `hL' h (dict h).1 (dict h).2 rfl`.

Use `⟨γ, hγ, fun ρ τ e => H ρ τ e, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨γ', hγ', h1⟩` from `hmul h u hu`. Use `⟨γ', hγ', _, h1, fun ρ τ e => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mat (dict h).2 τ * mat (archMat V th rfl x0 u (dict h).1) τ = archM V (θ ρ) (γ * h * u) * x₀ (tauE D ρ)`. Rewrite using `[hcen _ τ ρ e, H ρ τ e, archM_mul' V _ (γ * h) u]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (x₀ _), Matrix.mul_nonsing_inv _ ((hN (dict h).1).det_unit ρ), Matrix.one_mul]`.
-/
theorem baseDict_of_frames (V : HSp D) {r : ℕ} (hr : V.rank = r) {Comp : Type} (X : Comp → Data D.host.E r)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (Kf : Subgroup (GA D V))
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (th th' : ∀ k, (X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hth : ∀ k τ, IsInfEmb τ.1 (th k τ)) (hth' : ∀ k τ, IsInfEmb τ.1 (th' k τ))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hΨ : ∀ k τ, τ ∈ (X k).Ψ ↔ ∃ ρ, τ = tauE D ρ) (hW : ∀ k, ModelW V hr (X k)) (hO : ∀ k, IsOrthogonalFrame (X k) x₀)
    (hD : DictIsUnif V dict Kf th hr)
    (hL : ∀ h, ∃ γ ∈ GQ V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th' (dict h).1 τ) (γ * h)) * x₀ τ.1) :
    ∃ x, BaseDict θ V hr X dict Kf x := by
  subst hr
  have hre : ∀ M : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) M = M := fun M => rfl
  obtain ⟨-, -, ⟨x0, hx0, hmul⟩, -, -, hfib⟩ := hD
  have e1 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th k τ = θ ρ := fun k τ ρ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth k τ) (e ▸ hθ ρ)
  have e2 : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → th' k τ = θ ρ := fun k τ ρ e =>
    GlobalTheory.SmoothForms.RealPts.infEmb_unique τ.1 _ _ (hth' k τ) (e ▸ hθ ρ)
  have hN : ∀ k, NegFirst V (X k).p0 fun ρ => x₀ (tauE D ρ) := fun k =>
    negFirst_of_orth V (X k) (hW k) (fun ρ => (hΨ k _).2 ⟨ρ, rfl⟩) x₀ (hO k)
  have hL' : ∀ h k (y : Frame (X k).Ψ V.rank), dict h = ⟨k, y⟩ → ∃ γ ∈ GQ V, ∀ ρ (τ : (X k).Ψ), τ.1 = tauE D ρ →
      mat y τ = archM V (θ ρ) (γ * h) * x₀ (tauE D ρ) := by
    intro h k y e
    have := hL h
    rw [e] at this
    obtain ⟨γ, hγ, H⟩ := this
    refine ⟨γ, hγ, fun ρ τ eτ => ?_⟩
    have := H τ
    rw [hre, e2 k τ ρ eτ, eτ] at this
    exact this
  have hmul' : ∀ g k (y : Frame (X k).Ψ V.rank), dict g = ⟨k, y⟩ → ∀ u ∈ GinfC V, ∃ γ' ∈ (X k).Γ,
      dict (g * u) = ⟨k, lact γ' (rmul y (archMat V th rfl x0 u k))⟩ := by
    intro g k y e u hu
    have := hmul g u hu
    rw [e] at this
    exact this
  have hA : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ =
      (mat (x0 k) τ)⁻¹ * archM V (θ ρ) u * mat (x0 k) τ := by
    intro k τ ρ e u
    rw [← e1 k τ ρ e]
    rfl
  have hcen : ∀ k (τ : (X k).Ψ) ρ, τ.1 = tauE D ρ → ∀ u, mat (archMat V th rfl x0 u k) τ =
      (x₀ (tauE D ρ))⁻¹ * archM V (θ ρ) u * x₀ (tauE D ρ) := by
    intro k τ ρ e
    obtain ⟨g0, hg0⟩ := (hx0 k).2
    obtain ⟨γ0, hγ0, H0⟩ := hL' g0 k _ hg0
    have H0' := H0 ρ τ e
    set a := archM V (θ ρ) (γ0 * g0) with ha
    set x := x₀ (tauE D ρ) with hx
    have hxu : IsUnit x.det := (hN k).det_unit ρ
    have hau : IsUnit a.det := archM_det_unit _ _ _
    have haxu : IsUnit (a * x).det := by rw [Matrix.det_mul]; exact hau.mul hxu
    haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
    haveI : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
      inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))
    have hc : ∀ w, w * a = a * w := by
      refine GlobalTheory.central_of_countable_commutators_unitary V.rank (gramAt D V ρ) a
        (Set.range fun M : Matrix (Fin V.rank) (Fin V.rank) D.host.E => M.map (tauE D ρ))
        (GlobalTheory.SmoothForms.RealPts.gramAt_herm V ρ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) hau
        (Set.countable_range _) fun Z hZ t => ?_
      have hZ' : Zᴴ * gramAt D V ρ + gramAt D V ρ * Z = 0 := hZ
      have hU : NormedSpace.exp (t • Z) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := by
        refine exp_unitary_of_lie (GlobalTheory.SmoothForms.RealPts.gramAt_unit V ρ) ?_
        rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hZ', smul_zero]
      obtain ⟨u, hu, huU⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2
        (fun ρ' => if ρ' = ρ then NormedSpace.exp (t • Z) else 1) (fun ρ' => by
          by_cases h : ρ' = ρ
          · subst h; simpa using hU
          · simp [h, Formalism.QuantumDeterminants.UH])
      have hUu : archM V (θ ρ) u = NormedSpace.exp (t • Z) := by
        have := huU ρ
        rw [if_pos rfl] at this
        exact this
      have hinv : NormedSpace.exp (t • Z) * NormedSpace.exp (-(t • Z)) = 1 := by
        rw [← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
        simp
      generalize NormedSpace.exp (t • Z) = U at hUu hinv
      generalize NormedSpace.exp (-(t • Z)) = U' at hinv
      obtain ⟨γ', -, h1⟩ := hmul' g0 k _ hg0 u hu
      obtain ⟨γ'', hγ'', h2⟩ := hL' _ k _ h1
      have h3 := h2 ρ τ e
      obtain ⟨δ, hδ⟩ := archM_rational V (γ'' * γ0⁻¹) (mul_mem hγ'' (inv_mem hγ0))
      have h4 : γ'' * (g0 * u) = (γ'' * γ0⁻¹) * (γ0 * g0) * u := by group
      rw [h4, archM_mul', archM_mul', hδ _ _ (hθ ρ), ← ha, hUu] at h3
      change γ'.1.map τ.1 * (mat (x0 k) τ * mat (archMat V th rfl x0 u k) τ) = _ at h3
      rw [hA k τ ρ e, H0', hUu, e, ← Matrix.mul_assoc (a * x), ← Matrix.mul_assoc (a * x),
        Matrix.mul_nonsing_inv _ haxu, Matrix.one_mul, ← hx] at h3
      have h5 : γ'.1.map (tauE D ρ) * (U * a) = δ.1.map (tauE D ρ) * a * U := by
        have := congrArg (· * x⁻¹) h3
        simpa only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hxu, Matrix.mul_one] using this
      refine ⟨(γ'⁻¹).1 * δ.1, ?_⟩
      have h6 : (γ'⁻¹).1.map (tauE D ρ) * γ'.1.map (tauE D ρ) = 1 := by
        rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
      show ((γ'⁻¹).1 * δ.1).map (tauE D ρ) = _
      rw [Matrix.map_mul, ← Matrix.one_mul (U * a), ← h6, Matrix.mul_assoc _ _ (U * a), h5]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U, hinv, Matrix.one_mul, Matrix.mul_nonsing_inv _ hau, Matrix.mul_one]
    intro u
    rw [hA k τ ρ e, H0', Matrix.mul_inv_rev, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹, Matrix.mul_assoc x⁻¹,
      Matrix.mul_assoc a⁻¹, ← Matrix.mul_assoc _ a, hc, Matrix.mul_assoc a, ← Matrix.mul_assoc a⁻¹,
      Matrix.nonsing_inv_mul _ hau, Matrix.one_mul]
  refine ⟨fun ρ => x₀ (tauE D ρ), fun k => ⟨⟨hΨ k, hW k⟩, hN k, ?_⟩, fun h => ?_, hfib⟩
  · obtain ⟨g, hg⟩ := (hx0 k).2
    exact ⟨g, by rw [hg]⟩
  · obtain ⟨γ, hγ, H⟩ := hL' h (dict h).1 (dict h).2 rfl
    refine ⟨γ, hγ, fun ρ τ e => H ρ τ e, fun u hu => ?_⟩
    obtain ⟨γ', hγ', h1⟩ := hmul h u hu
    refine ⟨γ', hγ', _, h1, fun ρ τ e => ?_⟩
    change mat (dict h).2 τ * mat (archMat V th rfl x0 u (dict h).1) τ =
      archM V (θ ρ) (γ * h * u) * x₀ (tauE D ρ)
    rw [hcen _ τ ρ e, H ρ τ e, archM_mul' V _ (γ * h) u]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (x₀ _), Matrix.mul_nonsing_inv _ ((hN (dict h).1).det_unit ρ), Matrix.one_mul]

/- English proof (translation)
Introduce `D T h j hj σ hσ θ hθ`. Take `⟨th, hr, hth, hD⟩` from `h.dictU j hj σ hσ`. Take `⟨hr', hW⟩` from `h.modelW j hj σ hσ`. Take `⟨hr'', g, e, F, ik, φ, th', -, -, hth', -, hL⟩` from `h.adPin j hj σ hσ`. Establish `hU` using `(h.unf j hj σ hσ).2.1`.

Establish `hin : ∀ k ρ, tauE D ρ ∈ ((T.U j σ).X k).Ψ` using `fun k ρ => ((hU k).2 _).2 (h.pins.1.2.2.2 ρ)`. Use `⟨hr, baseDict_of_frames _ hr _ _ _ θ hθ th th' hth hth' (T.x₀ j σ) (fun k τ => ⟨fun hτ => ?_, ?_⟩) hW (h.familyUniformisationBasePointOrthogonal j hj σ hσ) hD fun g => ?_⟩` and prove the remaining obligations. Take `⟨ρ, hρ⟩` from `(GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 (by`. Introduce and unpack `⟨ρ, hρ⟩`. Conclude with `(((T.U j σ).X k).cmType τ).1 hτ (hρ ▸ hin k ρ))`.

Conclude with `⟨ρ, hρ.symm⟩`. Introduce and unpack `⟨ρ, rfl⟩`. Conclude with `hin k ρ`. Take `⟨γ, hγ, -, -, H⟩` from `hL g`. Conclude with `⟨γ, hγ, H⟩`.
-/
theorem baseDict_core : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ θ : InfFam D, IsInfFam θ → ∃ (hr : (T.V j σ).rank = D.R.r) (x₀ : D.what₂.Tau → Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ), BaseDict θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.Kf j σ) x₀ := by
  intro D T h j hj σ hσ θ hθ
  obtain ⟨th, hr, hth, hD⟩ := h.dictU j hj σ hσ
  obtain ⟨hr', hW⟩ := h.modelW j hj σ hσ
  obtain ⟨hr'', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := h.adPin j hj σ hσ
  have hU := (h.unf j hj σ hσ).2.1
  have hin : ∀ k ρ, tauE D ρ ∈ ((T.U j σ).X k).Ψ := fun k ρ => ((hU k).2 _).2 (h.pins.1.2.2.2 ρ)
  refine ⟨hr, baseDict_of_frames _ hr _ _ _ θ hθ th th' hth hth' (T.x₀ j σ) (fun k τ => ⟨fun hτ => ?_, ?_⟩) hW
    (h.familyUniformisationBasePointOrthogonal j hj σ hσ) hD fun g => ?_⟩
  · obtain ⟨ρ, hρ⟩ := (GlobalTheory.SmoothForms.RealPts.tauE_cm D τ).2 (by
      rintro ⟨ρ, hρ⟩
      exact (((T.U j σ).X k).cmType τ).1 hτ (hρ ▸ hin k ρ))
    exact ⟨ρ, hρ.symm⟩
  · rintro ⟨ρ, rfl⟩
    exact hin k ρ
  · obtain ⟨γ, hγ, -, -, H⟩ := hL g
    exact ⟨γ, hγ, H⟩

end GlobalTheory.HolRead
