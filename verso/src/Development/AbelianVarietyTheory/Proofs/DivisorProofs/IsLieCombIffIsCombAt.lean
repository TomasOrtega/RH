import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroupStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames GlobalTheory.AllWt
open scoped Classical

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FlagTan

section Comb

open DeRham Cris MonObj

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]

def lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : epsR R ⟶ A :=
  (List.ofFn fun i => GrpTangent.epsScale (cf i) ≫ v i).prod

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, fun _ => rfl, rfl⟩`.
-/
theorem isLieComb_lieComb {n : ℕ} (cf : Fin n → R) (v : Fin n → (epsR R ⟶ A)) : IsLieComb cf v (lieComb cf v) :=
  ⟨_, fun _ => rfl, rfl⟩

/- English proof (translation)
The claim follows from `| 0, _, _, _, _ => by simpa [lieComb] using h0 | n + 1, cf, f, v, h => by rw [Fin.sum_univ_succ, lieComb, List.ofFn_succ, List.prod_cons] exact ha (hs (h 0) _) (rel_lieComb h0 ha hs (fun i => cf i.succ) fun i => h i.succ)`.
-/
theorem rel_lieComb {N : Type*} [AddCommMonoid N] [Module R N] {P : N → (epsR R ⟶ A) → Prop} (h0 : P 0 1)
    (ha : ∀ {f f' v v'}, P f v → P f' v' → P (f + f') (v * v'))
    (hs : ∀ {f v}, P f v → ∀ r : R, P (r • f) (GrpTangent.epsScale r ≫ v)) :
    ∀ {n : ℕ} (cf : Fin n → R) {f : Fin n → N} {v : Fin n → (epsR R ⟶ A)}, (∀ i, P (f i) (v i)) →
      P (∑ i, cf i • f i) (lieComb cf v)
  | 0, _, _, _, _ => by simpa [lieComb] using h0
  | n + 1, cf, f, v, h => by
    rw [Fin.sum_univ_succ, lieComb, List.ofFn_succ, List.prod_cons]
    exact ha (hs (h 0) _) (rel_lieComb h0 ha hs (fun i => cf i.succ) fun i => h i.succ)

/- English proof (translation)
The claim follows from `rel_lieComb (isLieImage_one_iff.2 (zero_mem _)) IsLieImage.add IsLieImage.smul cf h`.
-/
theorem isLieImage_lieComb {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (h : ∀ i, DeRham.IsLieImage (f i) (v i)) : DeRham.IsLieImage (∑ i, cf i • f i) (lieComb cf v) :=
  rel_lieComb (isLieImage_one_iff.2 (zero_mem _)) IsLieImage.add IsLieImage.smul cf h

/- English proof (translation)
The claim follows from `rel_lieComb ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩ IsKSValue.add IsKSValue.smul cf e`.
-/
theorem isKSValue_lieComb {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left}
    {h : IsGrpPullback A A' (epsRed R) i} {n : ℕ} (cf : Fin n → R) {f : Fin n → HdR A} {v : Fin n → (epsR R ⟶ A)}
    (e : ∀ k, IsKSValue h (f k) (v k)) : IsKSValue h (∑ k, cf k • f k) (lieComb cf v) :=
  rel_lieComb ⟨0, ⟨0, zero_mem _, fun _ => (LinearMap.zero_apply _).trans (by simp)⟩, isLieImage_one_iff.2 (zero_mem _)⟩
    IsKSValue.add IsKSValue.smul cf e

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K]

/- English proof (translation)
The claim follows from `Chart.comb_push h cf v w`.
-/
theorem isLieComb_iff_isCombAt {A : Over (Sp K)} [GrpObj A] {x : Sp K ⟶ Xo.X} {π : A.left ⟶ Xo.univ.t.G.left}
    (h : IsGrpPullback A Xo.univ.t.G x π) {n : ℕ} (cf : Fin n → K) (v : Fin n → (epsR K ⟶ A)) (w : epsR K ⟶ A) :
    IsLieComb cf v w ↔ IsCombAt x (fun i => (v i).left ≫ π) cf (w.left ≫ π) :=
  Chart.comb_push h cf v w

def ksChg (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K) :
    (HIx Dw Φ → K) →ₗ[K] (HIx Dw Φ → K) where
  toFun M k := ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2
  map_add' M M' := by ext k; simp [mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r M := by ext k; simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ksChg_apply (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (k : HIx Dw Φ) :
    ksChg Φ g M k = ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2 := rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, ksChg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem ksChg_eq_mul (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) (τ : Φ) : (Matrix.of fun a b => ksChg Φ g M ⟨τ, a, b⟩) =
      (g (conjEmb τ.1)).transpose * (Matrix.of fun a b => M ⟨τ, a, b⟩) * g τ.1 := by
  ext a b
  simp only [Matrix.of_apply, ksChg_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `⟨τ, a, b⟩`. Establish `h : (Matrix.of fun a b => ksChg Φ g (ksChg Φ g' M) ⟨τ, a, b⟩) = Matrix.of fun a b => ksChg Φ (fun τ => g' τ * g τ) M ⟨τ, a, b⟩`. Simplify using `only [ksChg_eq_mul, Matrix.transpose_mul, Matrix.mul_assoc]`. Conclude with `congrFun (congrFun h a) b`.
-/
theorem ksChg_ksChg (Φ : Finset (E →+* ℂ)) (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (M : HIx Dw Φ → K) : ksChg Φ g (ksChg Φ g' M) = ksChg Φ (fun τ => g' τ * g τ) M := by
  funext ⟨τ, a, b⟩
  have h : (Matrix.of fun a b => ksChg Φ g (ksChg Φ g' M) ⟨τ, a, b⟩) =
      Matrix.of fun a b => ksChg Φ (fun τ => g' τ * g τ) M ⟨τ, a, b⟩ := by
    simp only [ksChg_eq_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  exact congrFun (congrFun h a) b

/- English proof (translation)
Use function extensionality and compare the values at `⟨τ, a, b⟩`. Establish `h` using `ksChg_eq_mul Φ (fun _ => 1) M τ`. Rewrite `h` using `[Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]`. Conclude with `congrFun (congrFun h a) b`.
-/
theorem ksChg_one (Φ : Finset (E →+* ℂ)) (M : HIx Dw Φ → K) : ksChg Φ (fun _ => 1) M = M := by
  funext ⟨τ, a, b⟩
  have h := ksChg_eq_mul Φ (fun _ => 1) M τ
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at h
  exact congrFun (congrFun h a) b

/- English proof (translation)
Take `⟨g', a', -, h'⟩` from `(frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm`. Establish `C` using `frChg_calculus E H Dw l Xo c K`. Establish `e` using `((frChg_exists_unique E H Dw l Xo c K y y).2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h).1 h') (C.2.1 y)).1`. Establish `e'` using `((frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')).1`. Conclude with `⟨g', a', h', congrFun e, congrFun e'⟩`.
-/
theorem exists_frChg_inv {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K} {a : K}
    {y y' : FrPt Xo c K} (h : FrChg g a y y') :
    ∃ g' a', FrChg g' a' y' y ∧ (∀ τ, g' τ * g τ = 1) ∧ ∀ τ, g τ * g' τ = 1 := by
  obtain ⟨g', a', -, h'⟩ := (frChg_exists_unique E H Dw l Xo c K y' y).1 h.1.symm
  have C := frChg_calculus E H Dw l Xo c K
  have e := ((frChg_exists_unique E H Dw l Xo c K y y).2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h).1 h') (C.2.1 y)).1
  have e' := ((frChg_exists_unique E H Dw l Xo c K y' y').2 _ _ _ _ ((C.1 _ _ _ _ _ _ _ h').1 h) (C.2.1 y')).1
  exact ⟨g', a', h', congrFun e, congrFun e'⟩

/- English proof (translation)
Simplify using `only [Finset.smul_sum, smul_smul, Finset.sum_smul, mul_assoc]`. Conclude with `(Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm`.
-/
theorem smul_sum_smul_sum {N α β γ : Type} [AddCommGroup N] [Module K N] [Fintype α] [Fintype β] [Fintype γ]
    (p : α → K) (M : α → β → K) (q : β → γ → K) (n : γ → N) :
    ∑ a, p a • ∑ b, M a b • ∑ k, q b k • n k = ∑ k, (∑ a, ∑ b, p a * M a b * q b k) • n k := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul, mul_assoc]
  exact (Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

open DeRham Cris in

/- English proof (translation)
Take `⟨g', a', h', e, -⟩` from `exists_frChg_inv h`. Take `⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hψ, hub, hhb, hrow⟩` from `hM`. Rewrite `hπ` using `[h.1]`. Take `⟨N, _, _, v, -, -, htan, hcomb, -, -⟩` from `GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x`. Use `choose n hn using fun σ k => (htan _).1 (y.tan σ k)`.

Establish `hn' : ∀ σ k, y'.u σ k = v (∑ j, g σ k j • n σ j)` using `fun σ k => by`. Use `h.2.1 σ k` as an intermediate fact. Rewrite `this` using `[show y.u σ = fun j => v (n σ j) from funext fun j => (hn σ j).symm, hcomb]`. Then use the resulting hypothesis. Establish `key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → N) (w : epsR K ⟶ A), (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j))` using `fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]`. Establish `hub' : ∀ σ k, (ub σ k).left ≫ π = v (∑ j, g σ k j • n σ j)` using `fun σ k => (hub σ k).trans (hn' σ k)`.

Establish `hu : ∀ σ k, (lieComb (g' σ k) (ub σ)).left ≫ π = v (n σ k)` using `fun σ k => by`. Rewrite using `[(key _ _ _ _ (hub' σ)).1 (isLieComb_lieComb _ _)]`. Use `congr 1`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [← Finset.sum_smul, ← Matrix.mul_apply, e, Matrix.one_apply]`. Simplify using the standard rewrite rules. Use `⟨A, _, A', _, π, π', i, hi, ψ, fun σ k => lieComb (g' σ k) (ub σ), fun q => ∑ j, g' q.1 q.2 j • hb ⟨q.1, j⟩, hπ, hπ', hiπ, hψ, fun σ k => (hu σ k).trans (hn σ k), fun σ k => isLieImage_lieComb _ (hhb σ), fun τ a => ?_⟩` and prove the remaining obligations. Use `choose w hw f hf hd hv using hrow τ`. Use `⟨lieComb (fun a' => g (conjEmb τ.1) a' a) w, (key _ _ _ _ (hu τ.1)).2 ?_, ∑ a', g (conjEmb τ.1) a' a • f a', Submodule.sum_mem _ fun a' _ => Submodule.smul_mem _ _ (hf a'), fun ⟨σ, k⟩ => ?_, isKSValue_lieComb _ hv⟩` and prove the remaining obligations.

Rewrite using `[(key _ _ _ _ fun a' => (key _ _ _ _ (hub' τ.1)).1 (hw a')).1 (isLieComb_lieComb _ _)]`. Use `congr 1`. Conclude with `smul_sum_smul_sum _ (fun a' b' => M' ⟨τ, a', b'⟩) _ _`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul]`. Distinguish the cases in `hσ : σ = conjEmb τ.1`.

Substitute `hσ` using the available equality. Use `congrFun (congrFun (e (conjEmb τ.1)) k) a` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `[hσ]`.
-/
theorem IsKS.of_frChg {Φ : Finset (E →+* ℂ)} {g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K}
    {a : K} {y y' : FrPt Xo c K} (h : FrChg g a y y') {x' : Sp (DualNumber K) ⟶ Xo.X} {M' : HIx Dw Φ → K}
    (hM : IsKS Φ y' x' M') : IsKS Φ y x' (ksChg Φ g M') := by
  obtain ⟨g', a', h', e, -⟩ := exists_frChg_inv h
  obtain ⟨A, _, A', _, π, π', i, hi, ψ, ub, hb, hπ, hπ', hiπ, hψ, hub, hhb, hrow⟩ := hM
  rw [h.1] at hπ
  obtain ⟨N, _, _, v, -, -, htan, hcomb, -, -⟩ := GlobalTheory.T.exists_tangent_module_universal_group E H Dw l Xo K y.x
  choose n hn using fun σ k => (htan _).1 (y.tan σ k)
  have hn' : ∀ σ k, y'.u σ k = v (∑ j, g σ k j • n σ j) := fun σ k => by
    have := h.2.1 σ k
    rwa [show y.u σ = fun j => v (n σ j) from funext fun j => (hn σ j).symm, hcomb] at this
  have key : ∀ {m : ℕ} (cf : Fin m → K) (u : Fin m → (epsR K ⟶ A)) (b : Fin m → N) (w : epsR K ⟶ A),
      (∀ j, (u j).left ≫ π = v (b j)) → (IsLieComb cf u w ↔ w.left ≫ π = v (∑ j, cf j • b j)) :=
    fun cf u b w hu => by rw [isLieComb_iff_isCombAt hπ, funext hu, hcomb]
  have hub' : ∀ σ k, (ub σ k).left ≫ π = v (∑ j, g σ k j • n σ j) := fun σ k => (hub σ k).trans (hn' σ k)
  have hu : ∀ σ k, (lieComb (g' σ k) (ub σ)).left ≫ π = v (n σ k) := fun σ k => by
    rw [(key _ _ _ _ (hub' σ)).1 (isLieComb_lieComb _ _)]
    congr 1
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, e, Matrix.one_apply]
    simp
  refine ⟨A, _, A', _, π, π', i, hi, ψ, fun σ k => lieComb (g' σ k) (ub σ),
    fun q => ∑ j, g' q.1 q.2 j • hb ⟨q.1, j⟩, hπ, hπ', hiπ, hψ, fun σ k => (hu σ k).trans (hn σ k),
    fun σ k => isLieImage_lieComb _ (hhb σ), fun τ a => ?_⟩
  choose w hw f hf hd hv using hrow τ
  refine ⟨lieComb (fun a' => g (conjEmb τ.1) a' a) w, (key _ _ _ _ (hu τ.1)).2 ?_,
    ∑ a', g (conjEmb τ.1) a' a • f a', Submodule.sum_mem _ fun a' _ => Submodule.smul_mem _ _ (hf a'),
    fun ⟨σ, k⟩ => ?_, isKSValue_lieComb _ hv⟩
  · rw [(key _ _ _ _ fun a' => (key _ _ _ _ (hub' τ.1)).1 (hw a')).1 (isLieComb_lieComb _ _)]
    congr 1
    exact smul_sum_smul_sum _ (fun a' b' => M' ⟨τ, a', b'⟩) _ _
  · simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul]
    by_cases hσ : σ = conjEmb τ.1
    · subst hσ
      have := congrFun (congrFun (e (conjEmb τ.1)) k) a
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    · simp [hσ]

/- English proof (translation)
Use `⟨fun k => k.of_frChg h, fun k => ?_⟩` and prove the remaining obligations. Take `⟨g', a', h', -, e⟩` from `exists_frChg_inv h`. Use `IsKS.of_frChg h' (M' := ksChg Φ g M') k` as an intermediate fact. Rewrite `this` using `[ksChg_ksChg, funext e, ksChg_one]`. Then use the resulting hypothesis.
-/
theorem isKS_frChg_iff (Φ : Finset (E →+* ℂ)) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (a : K) (y y' : FrPt Xo c K) (h : FrChg g a y y') (x' : Sp (DualNumber K) ⟶ Xo.X) (M' : HIx Dw Φ → K) :
    IsKS Φ y' x' M' ↔ IsKS Φ y x'
      (fun k => ∑ a', ∑ b', g (conjEmb k.1.1) a' k.2.1 * M' ⟨k.1, a', b'⟩ * g k.1.1 b' k.2.2) := by
  refine ⟨fun k => k.of_frChg h, fun k => ?_⟩
  obtain ⟨g', a', h', -, e⟩ := exists_frChg_inv h
  have := IsKS.of_frChg h' (M' := ksChg Φ g M') k
  rwa [ksChg_ksChg, funext e, ksChg_one] at this

end GlobalTheory.FlagTan
