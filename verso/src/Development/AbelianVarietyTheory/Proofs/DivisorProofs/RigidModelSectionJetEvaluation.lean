import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.JetIntegral

section Alg

open MvPolynomial

variable {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem topCoeff_mk {k : ℕ} (p : MvPolynomial (Fin k) R) :
    topCoeff R k (Ideal.Quotient.mk _ p) = coeff (topMon k) p := rfl

def aug (R : Type) [CommRing R] (k : ℕ) : EpsAlg R k →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval fun _ => 0) fun p hp => by
    refine (show sqIdeal R k ≤ RingHom.ker (aeval (fun _ => 0) : MvPolynomial (Fin k) R →ₐ[R] R) from ?_) hp
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    simp [RingHom.mem_ker]

/- English proof (translation)
Use `show aeval (fun _ => 0) p = _`. Simplify using `[constantCoeff_eq]`.
-/
theorem aug_mk {k : ℕ} (p : MvPolynomial (Fin k) R) : aug R k (Ideal.Quotient.mk _ p) = coeff 0 p := by
  show aeval (fun _ => 0) p = _
  simp [constantCoeff_eq]

/- English proof (translation)
Rewrite using `[eps, aug_mk]`. Simplify using the standard rewrite rules.
-/
theorem aug_eps {k : ℕ} (a : Fin k) : aug R k (eps R a) = 0 := by
  rw [eps, aug_mk]
  simp

/- English proof (translation)
Rewrite using `[← rename_X, killCompl_rename_app]`.
-/
theorem killCompl_X_self {k i : ℕ} {σ : Fin k → Fin i} (hσ : Function.Injective σ) (b : Fin k) :
    killCompl hσ (X (σ b) : MvPolynomial (Fin i) R) = X b := by
  rw [← rename_X, killCompl_rename_app]

/- English proof (translation)
Rewrite using `[killCompl, aeval_X, dif_neg ha]`.
-/
theorem killCompl_X_of_notMem {k i : ℕ} {σ : Fin k → Fin i} (hσ : Function.Injective σ) {a : Fin i}
    (ha : a ∉ Set.range σ) : killCompl hσ (X a : MvPolynomial (Fin i) R) = 0 := by
  rw [killCompl, aeval_X, dif_neg ha]

def kill (R : Type) [CommRing R] {k i : ℕ} {σ : Fin k → Fin i} (hσ : Function.Injective σ) :
    EpsAlg R i →ₐ[R] EpsAlg R k :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R (sqIdeal R k)).comp (killCompl hσ)) fun p hp => by
    refine (show sqIdeal R i ≤ RingHom.ker ((Ideal.Quotient.mkₐ R (sqIdeal R k)).comp (killCompl hσ)) from ?_) hp
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    by_cases ha : a ∈ Set.range σ
    · obtain ⟨b, rfl⟩ := ha
      simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.comp_apply, map_pow, killCompl_X_self]
      rw [sq]
      exact eps_mul_self R b
    · simp [RingHom.mem_ker, killCompl_X_of_notMem hσ ha]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kill_mk {k i : ℕ} {σ : Fin k → Fin i} (hσ : Function.Injective σ) (p : MvPolynomial (Fin i) R) :
    kill R hσ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (killCompl hσ p) := rfl

/- English proof (translation)
Rewrite using `[eps, kill_mk, killCompl_X_self, eps]`.
-/
theorem kill_eps_self {k i : ℕ} {σ : Fin k → Fin i} (hσ : Function.Injective σ) (b : Fin k) :
    kill R hσ (eps R (σ b)) = eps R b := by
  rw [eps, kill_mk, killCompl_X_self, eps]

/- English proof (translation)
Rewrite using `[eps, kill_mk, killCompl_X_of_notMem hσ ha, map_zero]`.
-/
theorem kill_eps_of_notMem {k i : ℕ} {σ : Fin k → Fin i} (hσ : Function.Injective σ) {a : Fin i}
    (ha : a ∉ Set.range σ) : kill R hσ (eps R a) = 0 := by
  rw [eps, kill_mk, killCompl_X_of_notMem hσ ha, map_zero]

/- English proof (translation)
Simplify using `[topMon, Finsupp.finsetSum_apply, Finsupp.single_apply]`.
-/
theorem topMon_apply {k : ℕ} (a : Fin k) : topMon k a = 1 := by
  simp [topMon, Finsupp.finsetSum_apply, Finsupp.single_apply]

/- English proof (translation)
Take `⟨u, rfl⟩` from `Ideal.Quotient.mk_surjective u`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[← map_mul, topCoeff_mk, topCoeff_mk, aug_mk, coeff_mul, Finset.sum_eq_single (0, topMon i)]`. Introduce and unpack `⟨m, n⟩ hmn hne`. Establish `e : m + n = topMon i` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hmn`.

Establish `hle : ∀ a, m a + n a = 1` using `fun a => by rw [← topMon_apply a, ← e]; rfl`. Establish `hS : n.support ≠ Finset.univ` using `fun h => hne (by`. Establish `hn : ∀ a, n a ≠ 0` using `fun a => Finsupp.mem_support_iff.1 (h ▸ Finset.mem_univ a)`. Use `Prod.ext (Finsupp.ext fun a => ?_) (Finsupp.ext fun a => ?_)` and prove the remaining obligations. Use `hle a` as an intermediate fact.

Use `hn a` as an intermediate fact. Use `show m a = 0`. Use linear arithmetic over natural numbers and integers. Use `hle a` as an intermediate fact. Use `hn a` as an intermediate fact.

Use `show n a = _`. Rewrite using `[topMon_apply]`. Use the proof step `omega)`. Establish `hc : n.support.card < i`. Simplify using `using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)`.

Establish `hσ` using `(n.support.orderEmbOfFin rfl).injective`. Establish `h0` using `hz _ hc _ hσ`. Rewrite `h0` using `[kill_mk, topCoeff_mk, coeff_killCompl]`. Establish `e2 : (topMon n.support.card).mapDomain (n.support.orderEmbOfFin rfl) = n`. Use extensionality with `a`.

Distinguish the cases in `ha : a ∈ Set.range (n.support.orderEmbOfFin rfl)`. Take `⟨b, rfl⟩` from `ha`. Rewrite using `[Finsupp.mapDomain_apply hσ, topMon_apply]`. Establish `h1` using `Finsupp.mem_support_iff.1 (n.support.orderEmbOfFin_mem rfl b)`. Use `hle (n.support.orderEmbOfFin rfl b)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.mapDomain_notin_range _ _ ha]`. Rewrite `ha` using `[Finset.range_orderEmbOfFin]`. Conclude with `(Finsupp.notMem_support_iff.1 ha).symm`. Rewrite `h0` using `[e2]`.

Simplify using `[h0]`. Introduce `h`. Conclude with `absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add _)) h`.
-/
theorem topCoeff_mul {i : ℕ} (u z : EpsAlg R i)
    (hz : ∀ k < i, ∀ (σ : Fin k → Fin i) (hσ : Function.Injective σ), topCoeff R k (kill R hσ z) = 0) :
    topCoeff R i (u * z) = aug R i u * topCoeff R i z := by
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [← map_mul, topCoeff_mk, topCoeff_mk, aug_mk, coeff_mul, Finset.sum_eq_single (0, topMon i)]
  · rintro ⟨m, n⟩ hmn hne
    have e : m + n = topMon i := Finset.HasAntidiagonal.mem_antidiagonal.1 hmn
    have hle : ∀ a, m a + n a = 1 := fun a => by rw [← topMon_apply a, ← e]; rfl
    have hS : n.support ≠ Finset.univ := fun h => hne (by
      have hn : ∀ a, n a ≠ 0 := fun a => Finsupp.mem_support_iff.1 (h ▸ Finset.mem_univ a)
      refine Prod.ext (Finsupp.ext fun a => ?_) (Finsupp.ext fun a => ?_)
      · have := hle a; have := hn a; show m a = 0; omega
      · have := hle a; have := hn a; show n a = _; rw [topMon_apply]; omega)
    have hc : n.support.card < i := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.2 hS)
    have hσ := (n.support.orderEmbOfFin rfl).injective
    have h0 := hz _ hc _ hσ
    rw [kill_mk, topCoeff_mk, coeff_killCompl] at h0
    have e2 : (topMon n.support.card).mapDomain (n.support.orderEmbOfFin rfl) = n := by
      ext a
      by_cases ha : a ∈ Set.range (n.support.orderEmbOfFin rfl)
      · obtain ⟨b, rfl⟩ := ha
        rw [Finsupp.mapDomain_apply hσ, topMon_apply]
        have h1 := Finsupp.mem_support_iff.1 (n.support.orderEmbOfFin_mem rfl b)
        have := hle (n.support.orderEmbOfFin rfl b)
        omega
      · rw [Finsupp.mapDomain_notin_range _ _ ha]
        rw [Finset.range_orderEmbOfFin] at ha
        exact (Finsupp.notMem_support_iff.1 ha).symm
    rw [e2] at h0
    simp [h0]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add _)) h

def epsMap (f : R →+* R') (k : ℕ) : EpsAlg R k →+* EpsAlg R' k :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    simp only [SetLike.mem_coe, Ideal.mem_comap, map_pow, map_X]
    exact Ideal.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem epsMap_mk (f : R →+* R') {k : ℕ} (p : MvPolynomial (Fin k) R) :
    epsMap f k (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

/- English proof (translation)
Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[epsMap_mk, topCoeff_mk, topCoeff_mk, coeff_map]`.
-/
theorem topCoeff_epsMap (f : R →+* R') {k : ℕ} (z : EpsAlg R k) :
    topCoeff R' k (epsMap f k z) = f (topCoeff R k z) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [epsMap_mk, topCoeff_mk, topCoeff_mk, coeff_map]

/- English proof (translation)
Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Use `show aug R' k (epsMap f k (Ideal.Quotient.mk _ p)) = f (aug R k (Ideal.Quotient.mk _ p))`. Rewrite using `[epsMap_mk, aug_mk, aug_mk, coeff_map]`.
-/
theorem aug_epsMap (f : R →+* R') {k : ℕ} :
    (aug R' k : EpsAlg R' k →+* R').comp (epsMap f k) = f.comp (aug R k : EpsAlg R k →+* R) := by
  refine RingHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  show aug R' k (epsMap f k (Ideal.Quotient.mk _ p)) = f (aug R k (Ideal.Quotient.mk _ p))
  rw [epsMap_mk, aug_mk, aug_mk, coeff_map]

/- English proof (translation)
Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Rewrite using `[RingHom.comp_apply, epsMap_mk, epsMap_mk, epsMap_mk, map_map]`.
-/
theorem epsMap_comp {R'' : Type} [CommRing R''] (f : R →+* R') (g : R' →+* R'') {k : ℕ} :
    (epsMap g k).comp (epsMap f k) = epsMap (g.comp f) k := by
  refine RingHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [RingHom.comp_apply, epsMap_mk, epsMap_mk, epsMap_mk, map_map]

/- English proof (translation)
Use `RingHom.ext fun r => ?_` and prove the remaining obligations. Use `show epsMap f k (Ideal.Quotient.mk _ (C r)) = Ideal.Quotient.mk _ (C (f r))`. Rewrite using `[epsMap_mk, map_C]`.
-/
theorem epsMap_algebraMap (f : R →+* R') {k : ℕ} :
    (epsMap f k).comp (algebraMap R (EpsAlg R k)) = (algebraMap R' (EpsAlg R' k)).comp f := by
  refine RingHom.ext fun r => ?_
  show epsMap f k (Ideal.Quotient.mk _ (C r)) = Ideal.Quotient.mk _ (C (f r))
  rw [epsMap_mk, map_C]

/- English proof (translation)
Simplify using `[epsIncl, DualNumber.lift_apply_apply, Algebra.ofId_apply]`.
-/
theorem epsIncl_apply {k : ℕ} (a : Fin k) (d : DualNumber R) :
    epsIncl R a d = algebraMap R _ d.fst + algebraMap R _ d.snd * eps R a := by
  simp [epsIncl, DualNumber.lift_apply_apply, Algebra.ofId_apply]

/- English proof (translation)
Use `RingHom.ext fun d => ?_` and prove the remaining obligations. Use `show epsMap f k (epsIncl R a d) = epsIncl R' a (Chart.dualMapR f d)`. Establish `h` using `fun r => RingHom.congr_fun (epsMap_algebraMap f (k := k)) r`. Simplify using `only [RingHom.comp_apply] at h`. Establish `he : epsMap f k (eps R a) = eps R' a` using `by rw [eps, epsMap_mk, map_X, eps]`.

Rewrite using `[epsIncl_apply, epsIncl_apply, map_add, map_mul, h, h, he]`. Simplify using `[Chart.dualMapR]`.
-/
theorem epsMap_epsIncl (f : R →+* R') {k : ℕ} (a : Fin k) :
    (epsMap f k).comp (epsIncl R a : DualNumber R →+* EpsAlg R k) =
      (epsIncl R' a : DualNumber R' →+* EpsAlg R' k).comp (Chart.dualMapR f) := by
  refine RingHom.ext fun d => ?_
  show epsMap f k (epsIncl R a d) = epsIncl R' a (Chart.dualMapR f d)
  have h := fun r => RingHom.congr_fun (epsMap_algebraMap f (k := k)) r
  simp only [RingHom.comp_apply] at h
  have he : epsMap f k (eps R a) = eps R' a := by rw [eps, epsMap_mk, map_X, eps]
  rw [epsIncl_apply, epsIncl_apply, map_add, map_mul, h, h, he]
  simp [Chart.dualMapR]

/- English proof (translation)
Introduce `z hz`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective z`. Establish `h0 : coeff 0 p = 0` using `(aug_mk p).symm.trans hz`. Establish `hp : p ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin k) R))`. Rewrite using `[mem_ideal_span_X_image]`.

Introduce `m hm`. Assume the negation of the conclusion as `h`. Establish `: m = 0` using `Finsupp.ext fun a => by_contra fun ha => h ⟨a, trivial, ha⟩`. Conclude with `mem_support_iff.1 hm (this ▸ h0)`. Use `(show Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin k) R)) ≤ q.comap (Ideal.Quotient.mk _) from ?_) hp` and prove the remaining obligations.

Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, -, rfl⟩`. Establish `: eps R a * eps R a ∈ q` using `by rw [eps_mul_self]; exact q.zero_mem`. Conclude with `(hq.mem_or_mem this).elim id id`.
-/
theorem ker_aug_le {k : ℕ} (q : Ideal (EpsAlg R k)) [hq : q.IsPrime] :
    RingHom.ker (aug R k : EpsAlg R k →+* R) ≤ q := by
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  have h0 : coeff 0 p = 0 := (aug_mk p).symm.trans hz
  have hp : p ∈ Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin k) R)) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra h
    have : m = 0 := Finsupp.ext fun a => by_contra fun ha => h ⟨a, trivial, ha⟩
    exact mem_support_iff.1 hm (this ▸ h0)
  refine (show Ideal.span (X '' Set.univ : Set (MvPolynomial (Fin k) R)) ≤ q.comap (Ideal.Quotient.mk _) from ?_) hp
  refine Ideal.span_le.2 ?_
  rintro _ ⟨a, -, rfl⟩
  have : eps R a * eps R a ∈ q := by rw [eps_mul_self]; exact q.zero_mem
  exact (hq.mem_or_mem this).elim id id

/- English proof (translation)
Introduce `z`. Establish `hs : Function.Surjective (aug R k : EpsAlg R k →+* R)` using `fun r => ⟨algebraMap R _ r, (aug R k).commutes r⟩`. Establish `: z ∈ Set.range (PrimeSpectrum.comap (aug R k : EpsAlg R k →+* R))`. Rewrite using `[range_comap_of_surjective _ _ hs]`. Conclude with `ker_aug_le z.asIdeal (hq := z.isPrime)`.

Conclude with `this`.
-/
theorem spMap_aug_surjective {k : ℕ} : Function.Surjective (spMap (aug R k : EpsAlg R k →+* R)) := by
  intro z
  have hs : Function.Surjective (aug R k : EpsAlg R k →+* R) := fun r => ⟨algebraMap R _ r, (aug R k).commutes r⟩
  have : z ∈ Set.range (PrimeSpectrum.comap (aug R k : EpsAlg R k →+* R)) := by
    rw [range_comap_of_surjective _ _ hs]
    exact ker_aug_le z.asIdeal (hq := z.isPrime)
  exact this

end Alg

section Geo

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]
  {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C]

def spOver (f : A →ₐ[R] B) : Over.mk (spMap (algebraMap R B)) ⟶ Over.mk (spMap (algebraMap R A)) :=
  Over.homMk (spMap (f : A →+* B)) (spMap_comp_eq R f)

/- English proof (translation)
The claim follows from `Over.OverMorphism.ext (spMap_comp_spMap (f : A →+* B) (g : B →+* C))`.
-/
theorem spOver_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : spOver g ≫ spOver f = spOver (g.comp f) :=
  Over.OverMorphism.ext (spMap_comp_spMap (f : A →+* B) (g : B →+* C))

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left, eSec]`. Use `congr 1`.
-/
theorem one_left {S : Scheme.{0}} {H : Over S} [GrpObj H] (T : Over S) : (1 : T ⟶ H).left = T.hom ≫ eSec H := by
  rw [Hom.one_def, Over.comp_left, eSec]
  congr 1

/- English proof (translation)
Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Rewrite using `[one_left, eSec, ← hy]`. Use `show spMap (ψ : DualNumber R →+* B) ≫ y.left = spMap (algebraMap R B) ≫ _`. Rewrite using `[← Category.assoc, spMap_comp_spMap]`. Establish `: ψ = (Algebra.ofId R B).comp (TrivSqZeroExt.fstHom R R R)`.

Use `ext`. Simplify using `[h]`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem spOver_tangent {y : epsR R ⟶ G} (hy : IsTangent y) (ψ : DualNumber R →ₐ[R] B) (h : ψ DualNumber.eps = 0) :
    spOver ψ ≫ y = 1 := by
  refine Over.OverMorphism.ext ?_
  rw [one_left, eSec, ← hy]
  show spMap (ψ : DualNumber R →+* B) ≫ y.left = spMap (algebraMap R B) ≫ _
  rw [← Category.assoc, spMap_comp_spMap]
  have : ψ = (Algebra.ofId R B).comp (TrivSqZeroExt.fstHom R R R) := by
    ext
    simp [h]
  rw [this]
  rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]`.
-/
theorem comp_prod {S : Scheme.{0}} {H T T' : Over S} [GrpObj H] (h : T' ⟶ T) (l : List (T ⟶ H)) :
    h ≫ l.prod = (l.map (h ≫ ·)).prod := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.prod_cons, MonObj.comp_mul, ih, List.map_cons, List.prod_cons]

/- English proof (translation)
Rewrite using `[SecJet.epsPt, comp_prod, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `a`. Rewrite using `[← spOver_comp, Category.assoc]`. Both sides reduce to the same expression.
-/
theorem spOver_epsPt (y : epsR R ⟶ G) {k : ℕ} (g : EpsAlg R k →ₐ[R] B) :
    spOver g ≫ epsPt y k = (List.ofFn fun a : Fin k => spOver (g.comp (epsIncl R a)) ≫ y).prod := by
  rw [SecJet.epsPt, comp_prod, List.map_ofFn]
  congr 2
  funext a
  rw [← spOver_comp, Category.assoc]
  rfl

/- English proof (translation)
Simplify using `[epsIncl_apply]`.
-/
theorem epsIncl_eps {k : ℕ} (a : Fin k) : epsIncl R a DualNumber.eps = eps R a := by
  simp [epsIncl_apply]

/- English proof (translation)
Establish `h : spOver (aug R k) ≫ epsPt y k = 1`. Rewrite using `[spOver_epsPt]`. Use `List.prod_eq_one fun x hx => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `spOver_tangent hy _ (by rw [AlgHom.comp_apply, epsIncl_eps, aug_eps])`.

Establish `h1` using `congrArg (·.left) h`. Simplify using `only [one_left] at h1`. Use `h1.trans ?_` and prove the remaining obligations. Use `show spMap (RingHom.id R) ≫ eSec G = _`. Rewrite using `[show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id (CommRingCat.of R)]`.

Conclude with `Category.id_comp _`.
-/
theorem aug_epsPt {y : epsR R ⟶ G} (hy : IsTangent y) (k : ℕ) :
    spMap (aug R k : EpsAlg R k →+* R) ≫ (epsPt y k).left = eSec G := by
  have h : spOver (aug R k) ≫ epsPt y k = 1 := by
    rw [spOver_epsPt]
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hx
    exact spOver_tangent hy _ (by rw [AlgHom.comp_apply, epsIncl_eps, aug_eps])
  have h1 := congrArg (·.left) h
  simp only [one_left] at h1
  refine h1.trans ?_
  show spMap (RingHom.id R) ≫ eSec G = _
  rw [show spMap (RingHom.id R) = 𝟙 _ from Spec.map_id (CommRingCat.of R)]
  exact Category.id_comp _

/- English proof (translation)
Establish `h : spOver (kill R hσ) ≫ epsPt y i = epsPt y k`. Rewrite using `[spOver_epsPt, SecJet.epsPt, List.prod_ofFn, List.prod_ofFn]`. Use `(Fintype.prod_of_injective σ hσ _ _ (fun a ha => ?_) fun b => ?_).symm` and prove the remaining obligations. Conclude with `spOver_tangent hy _ (by rw [AlgHom.comp_apply, epsIncl_eps, kill_eps_of_notMem hσ ha])`. Establish `: (kill R hσ).comp (epsIncl R (σ b)) = epsIncl R b`.

Use `ext`. Simplify using `[epsIncl_eps, kill_eps_self]`. Rewrite using `[this]`. Both sides reduce to the same expression. Conclude with `congrArg (·.left) h`.
-/
theorem kill_epsPt [IsCommMonObj G] {y : epsR R ⟶ G} (hy : IsTangent y) {k i : ℕ} {σ : Fin k → Fin i}
    (hσ : Function.Injective σ) :
    spMap (kill R hσ : EpsAlg R i →+* EpsAlg R k) ≫ (epsPt y i).left = (epsPt y k).left := by
  have h : spOver (kill R hσ) ≫ epsPt y i = epsPt y k := by
    rw [spOver_epsPt, SecJet.epsPt, List.prod_ofFn, List.prod_ofFn]
    refine (Fintype.prod_of_injective σ hσ _ _ (fun a ha => ?_) fun b => ?_).symm
    · exact spOver_tangent hy _ (by rw [AlgHom.comp_apply, epsIncl_eps, kill_eps_of_notMem hσ ha])
    · have : (kill R hσ).comp (epsIncl R (σ b)) = epsIncl R b := by
        ext
        simp [epsIncl_eps, kill_eps_self]
      rw [this]
      rfl
  exact congrArg (·.left) h

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by rw [List.ofFn_zero, List.ofFn_zero, List.prod_nil, List.prod_nil, one_left, one_left, Category.assoc, PolBaseChange.eSec_comm hφ] exact Category.assoc _ _ _ | n + 1, u, v, h => by rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons] exact hφ.2 T …`.
-/
theorem prod_pullback {S S' : Scheme.{0}} {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {f : S' ⟶ S}
    {φ : H'.left ⟶ H.left} (hφ : IsGrpPullback H' H f φ) (T : Over S') :
    ∀ (n : ℕ) (u : Fin n → (T ⟶ H')) (v : Fin n → (Over.mk (T.hom ≫ f) ⟶ H)), (∀ a, (v a).left = (u a).left ≫ φ) →
      (List.ofFn v).prod.left = (List.ofFn u).prod.left ≫ φ
  | 0, _, _, _ => by
    rw [List.ofFn_zero, List.ofFn_zero, List.prod_nil, List.prod_nil, one_left, one_left, Category.assoc,
      PolBaseChange.eSec_comm hφ]
    exact Category.assoc _ _ _
  | n + 1, u, v, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact hφ.2 T _ _ _ _ (h 0) (prod_pullback hφ T n _ _ fun a => h a.succ)

/- English proof (translation)
Set `m : Over.mk ((epsT R' k).hom ≫ spMap f) ⟶ epsT R k` to `Over.homMk (spMap (epsMap f k)) (by`. Use `(spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)` and prove the remaining obligations. Rewrite using `[epsMap_algebraMap])`. Establish `h1 : m ≫ epsPt Y k = (List.ofFn fun a => m ≫ epsIn R a ≫ Y).prod`. Rewrite using `[SecJet.epsPt, comp_prod, List.map_ofFn]`.

Both sides reduce to the same expression. Use `Eq.trans (prod_pullback hφ (epsT R' k) k _ _ fun a => ?_).symm (congrArg (·.left) h1).symm` and prove the remaining obligations. Use `show spMap (epsMap f k) ≫ spMap (epsIncl R a : DualNumber R →+* EpsAlg R k) ≫ Y.left = (spMap (epsIncl R' a : DualNumber R' →+* EpsAlg R' k) ≫ y.left) ≫ φ`. Rewrite using `[Category.assoc, h, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, epsMap_epsIncl]`.
-/
theorem epsPt_pullback {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] {f : R →+* R'}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G (spMap f) φ) {Y : epsR R ⟶ G} {y : epsR R' ⟶ G'}
    (h : IsVecOver f φ Y y) (k : ℕ) :
    (epsPt y k).left ≫ φ = spMap (epsMap f k) ≫ (epsPt Y k).left := by
  let m : Over.mk ((epsT R' k).hom ≫ spMap f) ⟶ epsT R k := Over.homMk (spMap (epsMap f k)) (by
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    rw [epsMap_algebraMap])
  have h1 : m ≫ epsPt Y k = (List.ofFn fun a => m ≫ epsIn R a ≫ Y).prod := by
    rw [SecJet.epsPt, comp_prod, List.map_ofFn]
    rfl
  refine Eq.trans (prod_pullback hφ (epsT R' k) k _ _ fun a => ?_).symm (congrArg (·.left) h1).symm
  show spMap (epsMap f k) ≫ spMap (epsIncl R a : DualNumber R →+* EpsAlg R k) ≫ Y.left =
    (spMap (epsIncl R' a : DualNumber R' →+* EpsAlg R' k) ≫ y.left) ≫ φ
  rw [Category.assoc, h, ← Category.assoc, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, epsMap_epsIncl]

end Geo

section Val

open GlobalTheory.Points

variable {A A' : Type} [CommRing A] [CommRing A'] {X Y : Scheme.{0}}

/- English proof (translation)
Introduce `y _` and use `ht (show r y ∈ (⊤ : (Sp A).Opens) from trivial)`.
-/
theorem top_le_comp {x : Sp A ⟶ X} {V : X.Opens} (ht : ⊤ ≤ x ⁻¹ᵁ V) (r : Sp A' ⟶ Sp A) : ⊤ ≤ (r ≫ x) ⁻¹ᵁ V :=
  fun y _ => ht (show r y ∈ (⊤ : (Sp A).Opens) from trivial)

/- English proof (translation)
Introduce `y _` and use `by obtain ⟨z, rfl⟩ := hr y exact ht (show z ∈ (⊤ : (Sp A').Opens) from trivial)`.
-/
theorem top_le_of_surjective {x : Sp A ⟶ X} {V : X.Opens} {r : Sp A' ⟶ Sp A} (hr : Function.Surjective r)
    (ht : ⊤ ≤ (r ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := fun y _ => by
  obtain ⟨z, rfl⟩ := hr y
  exact ht (show z ∈ (⊤ : (Sp A').Opens) from trivial)

/- English proof (translation)
Introduce `_ hz` and use `⟨hU hz, hV hz⟩`.
-/
theorem top_le_inf {x : Sp A ⟶ X} {U V : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := fun _ hz => ⟨hU hz, hV hz⟩

/- English proof (translation)
Rewrite using `[valR, valR, dif_pos ht, dif_pos (top_le_comp ht _), ← Scheme.Hom.appLE_comp_appLE (spMap ρ) x V ⊤ ⊤ ht le_top]`. Establish `e` using `congrArg (fun q => q.hom ((x.appLE V ⊤ ht).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ))`. Use `Eq.trans ?_ e` and prove the remaining obligations. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply]`. Use `congr 2`.
-/
theorem valR_spMap (ρ : A →+* A') (x : Sp A ⟶ X) (V : X.Opens) (ht : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)) :
    valR (spMap ρ ≫ x) V a = ρ (valR x V a) := by
  rw [valR, valR, dif_pos ht, dif_pos (top_le_comp ht _),
    ← Scheme.Hom.appLE_comp_appLE (spMap ρ) x V ⊤ ⊤ ht le_top]
  have e := congrArg (fun q => q.hom ((x.appLE V ⊤ ht).hom a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ρ))
  refine Eq.trans ?_ e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  congr 2

/- English proof (translation)
Rewrite using `[valR_eq x V ht]`. Conclude with `a.isUnit.map _`.
-/
theorem isUnit_valR (x : Sp A ⟶ X) (V : X.Opens) (ht : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, V)ˣ) : IsUnit (valR x V a.val) := by
  rw [valR_eq x V ht]
  exact a.isUnit.map _

/- English proof (translation)
Use `(valR_appLE x p (U := ⊤) (fun _ _ => trivial) h _).trans ?_` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `valR_specMap (CommRingCat.ofHom f) a`.
-/
theorem valR_constFn (p : X ⟶ Sp A') (f : A' →+* A) (x : Sp A ⟶ X) (hx : x ≫ p = spMap f) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : A') : valR x U (constFn p U a) = f a := by
  refine (valR_appLE x p (U := ⊤) (fun _ _ => trivial) h _).trans ?_
  rw [hx]
  exact valR_specMap (CommRingCat.ofHom f) a

/- English proof (translation)
Rewrite using `[pull_U]`. Both sides reduce to the same expression.
-/
theorem top_le_pull_iff (L : LB X) (φ : Y ⟶ X) (x : Sp A ⟶ Y) (p : PUnit → L.ι) :
    ⊤ ≤ x ⁻¹ᵁ (L.pull φ).U p ↔ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (p ⟨⟩) := by
  rw [pull_U]
  rfl

/- English proof (translation)
Rewrite using `[pull_g, valR_comp]`. Conclude with `valR_res x _ h _`.
-/
theorem valR_pull_g (L : LB X) (φ : Y ⟶ X) (x : Sp A ⟶ Y) (p p' : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ ((L.pull φ).U p ⊓ (L.pull φ).U p')) :
    valR x _ ((L.pull φ).g p p').val = valR (x ≫ φ) _ (L.g (p ⟨⟩) (p' ⟨⟩)).val := by
  rw [pull_g, valR_comp]
  exact valR_res x _ h _

/- English proof (translation)
Rewrite using `[valR_comp]`. Conclude with `valR_res x _ h _`.
-/
theorem valR_secPull {L : LB X} (t : L.Sec) (φ : Y ⟶ X) (x : Sp A ⟶ Y) (p : PUnit → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ (L.pull φ).U p) :
    valR x _ ((secPull t φ).f p) = valR (x ≫ φ) _ (t.f (p ⟨⟩)) := by
  rw [valR_comp]
  exact valR_res x _ h _

/- English proof (translation)
Establish `h` using `top_le_inf hi hj`. Establish `e` using `congrArg (fun u => valR x (L.U i ⊓ L.U j) u.val) (ht i j)`. Simplify using `only [Units.val_mul, val_res] at e`. Rewrite `e` using `[valR_mul x _ h, valR_res x _ h, valR_res x _ h]`. Then use the resulting hypothesis.
-/
theorem valR_gen {L : LB X} {t : L.Gen} (ht : t.IsGen) (x : Sp A ⟶ X) {i j : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x _ (t.s i).val = valR x _ (L.g i j).val * valR x _ (t.s j).val := by
  have h := top_le_inf hi hj
  have e := congrArg (fun u => valR x (L.U i ⊓ L.U j) u.val) (ht i j)
  simp only [Units.val_mul, val_res] at e
  rwa [valR_mul x _ h, valR_res x _ h, valR_res x _ h] at e

/- English proof (translation)
Establish `h : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ L.U p ⊓ (M.U i' ⊓ L.U p'))` using `top_le_inf (top_le_inf hi hp) (top_le_inf hi' hp')`. Establish `h1 : M.U i ⊓ L.U p ⊓ (M.U i' ⊓ L.U p') ≤ M.U i ⊓ M.U i'` using `le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)`. Establish `h2 : M.U i ⊓ L.U p ⊓ (M.U i' ⊓ L.U p') ≤ L.U p ⊓ L.U p'` using `le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)`. Rewrite using `[← valR_res x h1 h, ← valR_res x h2 h]`. Use `(valR_mul x _ h _ _).symm.trans (congrArg _ ?_)` and prove the remaining obligations.

Conclude with `congrArg Units.val (inv_mul_cancel_right (res h1 (M.g i i')) (res h2 (L.g p p')))`.
-/
theorem valR_div_g (M L : LB X) (x : Sp A ⟶ X) {i i' : M.ι} {p p' : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ M.U i)
    (hi' : ⊤ ≤ x ⁻¹ᵁ M.U i') (hp : ⊤ ≤ x ⁻¹ᵁ L.U p) (hp' : ⊤ ≤ x ⁻¹ᵁ L.U p') :
    valR x _ ((M.div L).g (i, p) (i', p')).val * valR x _ (L.g p p').val = valR x _ (M.g i i').val := by
  have h : ⊤ ≤ x ⁻¹ᵁ (M.U i ⊓ L.U p ⊓ (M.U i' ⊓ L.U p')) := top_le_inf (top_le_inf hi hp) (top_le_inf hi' hp')
  have h1 : M.U i ⊓ L.U p ⊓ (M.U i' ⊓ L.U p') ≤ M.U i ⊓ M.U i' :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h2 : M.U i ⊓ L.U p ⊓ (M.U i' ⊓ L.U p') ≤ L.U p ⊓ L.U p' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  rw [← valR_res x h1 h, ← valR_res x h2 h]
  refine (valR_mul x _ h _ _).symm.trans (congrArg _ ?_)
  exact congrArg Units.val (inv_mul_cancel_right (res h1 (M.g i i')) (res h2 (L.g p p')))

/- English proof (translation)
Establish `h1 : valR x _ (M.g i i).val = 1`. Rewrite using `[← valR_res x (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i) hi, ← valR_one x _ hi]`. Conclude with `congrArg (fun u => valR x _ u.val) (hM.g_self i)`. Rewrite using `[valR_gen hw x (i := (i, p)) (j := (i, p')) (top_le_inf hi hp) (top_le_inf hi hp'), mul_right_comm, valR_div_g M L x hi hi hp hp', h1, _root_.one_mul]`.
-/
theorem valR_iso {L M : LB X} (hM : M.IsLB) {w : LB.Iso L M} (hw : w.IsGen) (x : Sp A ⟶ X) {i : M.ι} {p p' : L.ι}
    (hi : ⊤ ≤ x ⁻¹ᵁ M.U i) (hp : ⊤ ≤ x ⁻¹ᵁ L.U p) (hp' : ⊤ ≤ x ⁻¹ᵁ L.U p') :
    valR x _ (w.s (i, p)).val * valR x _ (L.g p p').val = valR x _ (w.s (i, p')).val := by
  have h1 : valR x _ (M.g i i).val = 1 := by
    rw [← valR_res x (le_inf le_rfl le_rfl : M.U i ≤ M.U i ⊓ M.U i) hi, ← valR_one x _ hi]
    exact congrArg (fun u => valR x _ u.val) (hM.g_self i)
  rw [valR_gen hw x (i := (i, p)) (j := (i, p')) (top_le_inf hi hp) (top_le_inf hi hp'), mul_right_comm,
    valR_div_g M L x hi hi hp hp', h1, _root_.one_mul]

/- English proof (translation)
Establish `h'` using `top_le_inf hi hp`. Establish `e` using `congrArg (valR x (M.U i ⊓ L.U p)) (h (i, p))`. Rewrite `e` using `[valR_mul x _ h', valR_res x _ h', valR_res x _ h']`. Then use the resulting hypothesis.
-/
theorem valR_secMaps {L M : LB X} {w : LB.Iso L M} {a : L.Sec} {b : M.Sec} (h : SecMaps w a b) (x : Sp A ⟶ X)
    {i : M.ι} {p : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ M.U i) (hp : ⊤ ≤ x ⁻¹ᵁ L.U p) :
    valR x _ (b.f i) = valR x _ (w.s (i, p)).val * valR x _ (a.f p) := by
  have h' := top_le_inf hi hp
  have e := congrArg (valR x (M.U i ⊓ L.U p)) (h (i, p))
  rwa [valR_mul x _ h', valR_res x _ h', valR_res x _ h'] at e

end Val

section Jet

open GlobalTheory.Points

/- English proof (translation)
Rewrite `h` using `[← aug_epsPt hy k]`. Conclude with `top_le_of_surjective (x := (epsPt y k).left) spMap_aug_surjective h`.
-/
theorem top_le_epsPt {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {y : epsR R ⟶ G} (hy : IsTangent y) (k : ℕ)
    {U : G.left.Opens} (h : ⊤ ≤ eSec G ⁻¹ᵁ U) : ⊤ ≤ (epsPt y k).left ⁻¹ᵁ U := by
  rw [← aug_epsPt hy k] at h
  exact top_le_of_surjective (x := (epsPt y k).left) spMap_aug_surjective h

variable {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] {y : epsR K ⟶ G}

/- English proof (translation)
Establish `h` using `top_le_epsPt hy k hi`. Establish `e : valR (A` using `EpsAlg K k) (epsPt y k).left (L.U i₀) ((secComb G.hom c b).f i₀) = ∑ a, c a • valR (A := EpsAlg K k) (epsPt y k).left (L.U i₀) ((b a).f i₀) := by`. Rewrite using `[valR_eq _ _ h]`. Simplify using `only [secComb]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← valR_eq, ← valR_eq, valR_constFn G.hom (algebraMap K _) _ (Over.w (epsPt y k)) _ h, Algebra.smul_def]`. Rewrite using `[jetFun_apply, jetVal, e, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, jetVal]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem jetFun_eq (hy : IsTangent y) {L : LB G.left} {i₀ : L.ι} (hi : ⊤ ≤ eSec G ⁻¹ᵁ L.U i₀) (c₀ : K) {r : ℕ}
    (b : Fin r → L.Sec) (k : ℕ) (c : Fin r → K) :
    jetFun y i₀ c₀ b k c = c₀⁻¹ * jetVal y k (L.U i₀) ((secComb G.hom c b).f i₀) := by
  have h := top_le_epsPt hy k hi
  have e : valR (A := EpsAlg K k) (epsPt y k).left (L.U i₀) ((secComb G.hom c b).f i₀) =
      ∑ a, c a • valR (A := EpsAlg K k) (epsPt y k).left (L.U i₀) ((b a).f i₀) := by
    rw [valR_eq _ _ h]
    simp only [secComb]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_mul, ← valR_eq, ← valR_eq, valR_constFn G.hom (algebraMap K _) _ (Over.w (epsPt y k)) _ h, Algebra.smul_def]
  rw [jetFun_apply, jetVal, e, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, jetVal]
  ring

/- English proof (translation)
The claim follows from `| 0, _, _, hk => absurd hk (Nat.not_lt_zero _) | i + 1, h, k, hk => by rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl · exact mem_filt j h.1 k hk · exact h.2`.
-/
theorem mem_filt {V : Type} [AddCommGroup V] [Module K V] (j : ℕ → V →ₗ[K] K) {v : V} :
    ∀ {i : ℕ}, v ∈ filt j i → ∀ k < i, j k v = 0
  | 0, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | i + 1, h, k, hk => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact mem_filt j h.1 k hk
    · exact h.2

/- English proof (translation)
Use `topCoeff_mul u _ fun k hk σ hσ => ?_` and prove the remaining obligations. Establish `e` using `valR_spMap (kill K hσ : EpsAlg K i →+* EpsAlg K k) (epsPt y i).left U (top_le_epsPt hy i hU) f`. Rewrite `e` using `[kill_epsPt hy hσ]`. Conclude with `(congrArg (topCoeff K k) e.symm).trans (h k hk)`.
-/
theorem topCoeff_mul_valR [IsCommMonObj G] (hy : IsTangent y) {U : G.left.Opens} (hU : ⊤ ≤ eSec G ⁻¹ᵁ U)
    (f : Γ(G.left, U)) {i : ℕ} (h : ∀ k < i, jetVal y k U f = 0) (u : EpsAlg K i) :
    topCoeff K i (u * valR (epsPt y i).left U f) = aug K i u * jetVal y i U f := by
  refine topCoeff_mul u _ fun k hk σ hσ => ?_
  have e := valR_spMap (kill K hσ : EpsAlg K i →+* EpsAlg K k) (epsPt y i).left U (top_le_epsPt hy i hU) f
  rw [kill_epsPt hy hσ] at e
  exact (congrArg (topCoeff K k) e.symm).trans (h k hk)

end Jet

section Model

open GlobalTheory.Points

variable {K : Type} [Field K] [NumberField K] {P : Out.PolAV (Sp K)} {AA : Over (Sp (𝓞 K))} [GrpObj AA]
  {φ : P.A.left ⟶ AA.left} {MM : RigLB AA} {N : ℕ} {w : LB.Iso (MM.L.pull φ) (lbPow P.L N)}

/- English proof (translation)
Establish `hex : ∃ p : PUnit → MM.L.ι, ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p)` using `⟨p, hp⟩`. Rewrite using `[rigVal, dif_pos hex]`. Establish `hq` using `hex.choose_spec`. Generalize the expression as in `hex.choose = q at hq`. Establish `he` using `PolBaseChange.eSec_comm hφ`.

Establish `tr : ∀ {p : PUnit → MM.L.ι}, ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) → ⊤ ≤ eSec P.A ⁻¹ᵁ (MM.L.pull φ).U p` using `fun {p} hp => (top_le_pull_iff MM.L φ (A := K) (eSec P.A) p).2 (by`. Use `(top_le_pull_iff MM.L (eSec AA) (spMap (algebraMap (𝓞 K) K)) p).1 hp` as an intermediate fact. Conclude with `he ▸ this)`. Establish `e1` using `valR_iso (A := K) (LB.isLB_linComb P.isLB _ _) hw (eSec P.A) hi (tr hq) (tr hp)`. Establish `e2` using `valR_gen MM.rigGen (spMap (algebraMap (𝓞 K) K)) hq hp`.

Establish `e3` using `valR_pull_g MM.L φ (A := K) (eSec P.A) q p (top_le_inf (A := K) (tr hq) (tr hp))`. Establish `e4` using `valR_pull_g MM.L (eSec AA) (spMap (algebraMap (𝓞 K) K)) q p (top_le_inf hq hp)`. Establish `e5` using `e3.trans ((congrArg (fun x : Sp K ⟶ AA.left => valR x _ (MM.L.g (q ⟨⟩) (p ⟨⟩)).val) he).trans e4.symm)`. Use `Eq.trans (congrArg _ e2) ?_` and prove the remaining obligations. Rewrite using `[← e1, e5, _root_.mul_assoc]`.
-/
theorem rigVal_eq (hφ : IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) {i₀ : (lbPow P.L N).ι}
    (hi : ⊤ ≤ eSec P.A ⁻¹ᵁ (lbPow P.L N).U i₀) (p : PUnit → MM.L.ι)
    (hp : ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p)) :
    rigVal w i₀ = valR (X := P.A.left) (eSec P.A) _ (w.s (i₀, p)).val *
      valR (X := Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s p).val := by
  have hex : ∃ p : PUnit → MM.L.ι,
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) := ⟨p, hp⟩
  rw [rigVal, dif_pos hex]
  have hq := hex.choose_spec
  generalize hex.choose = q at hq
  have he := PolBaseChange.eSec_comm hφ
  have tr : ∀ {p : PUnit → MM.L.ι},
      ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) →
      ⊤ ≤ eSec P.A ⁻¹ᵁ (MM.L.pull φ).U p := fun {p} hp =>
    (top_le_pull_iff MM.L φ (A := K) (eSec P.A) p).2 (by
      have := (top_le_pull_iff MM.L (eSec AA) (spMap (algebraMap (𝓞 K) K)) p).1 hp
      exact he ▸ this)
  have e1 := valR_iso (A := K) (LB.isLB_linComb P.isLB _ _) hw (eSec P.A) hi (tr hq) (tr hp)
  have e2 := valR_gen MM.rigGen (spMap (algebraMap (𝓞 K) K)) hq hp
  have e3 := valR_pull_g MM.L φ (A := K) (eSec P.A) q p (top_le_inf (A := K) (tr hq) (tr hp))
  have e4 := valR_pull_g MM.L (eSec AA) (spMap (algebraMap (𝓞 K) K)) q p (top_le_inf hq hp)
  have e5 := e3.trans ((congrArg (fun x : Sp K ⟶ AA.left => valR x _ (MM.L.g (q ⟨⟩) (p ⟨⟩)).val) he).trans e4.symm)
  refine Eq.trans (congrArg _ e2) ?_
  rw [← e1, e5, _root_.mul_assoc]

/- English proof (translation)
Use `letI := P.isAb.comm`. Establish `hy'` using `hy.isTangent hφ hY`. Establish `hja : spMap j ≫ spMap a = spMap (algebraMap (𝓞 K) K)` using `by rw [spMap_comp_spMap, hj]`. Establish `hpa` using `(top_le_pull_iff MM.L (eSec AA) (spMap a) p).2 hp`. Establish `hpK : ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p)`.

Rewrite using `[← hja]`. Conclude with `top_le_comp hpa _`. Establish `he` using `PolBaseChange.eSec_comm hφ`. Establish `hp0 : ⊤ ≤ eSec P.A ⁻¹ᵁ (MM.L.pull φ).U p` using `(top_le_pull_iff MM.L φ (A := K) (eSec P.A) p).2 (by`. Use `(top_le_pull_iff MM.L (eSec AA) (spMap (algebraMap (𝓞 K) K)) p).1 hpK` as an intermediate fact.

Conclude with `he ▸ this)`. Take `⟨ρ, hρ⟩` from `isUnit_valR (X := Sp (𝓞 K)) (spMap a) _ hpa (MM.rig.s p)`. Establish `hρK : valR (X` using `Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s p).val = j ρ := by`. Rewrite using `[hρ, ← hja]`. Conclude with `valR_spMap j _ _ hpa _`.

Establish `hiw : ⊤ ≤ eSec P.A ⁻¹ᵁ ((lbPow P.L N).U i₀ ⊓ (MM.L.pull φ).U p)` using `top_le_inf (A := K) hi hp0`. Take `⟨W, hW⟩` from `isUnit_valR (A := EpsAlg K i) (epsPt y i).left _ (top_le_epsPt hy' i hiw) (w.s (i₀, p))`. Establish `hW0 : aug K i W = valR (X` using `P.A.left) (eSec P.A) _ (w.s (i₀, p)).val := by`. Rewrite using `[hW, ← aug_epsPt hy' i]`. Conclude with `(valR_spMap (aug K i : EpsAlg K i →+* K) _ _ (top_le_epsPt hy' i hiw) _).symm`.

Establish `hrig : rigVal w i₀ = aug K i W * j ρ` using `by rw [rigVal_eq hφ hw hi p hpK, hρK, hW0]`. Establish `hW1 : aug K i W ≠ 0` using `(W.isUnit.map (aug K i)).ne_zero`. Establish `hρ1 : j ρ ≠ 0` using `(ρ.isUnit.map j).ne_zero`. Establish `hlow : ∀ k < i, jetVal y k _ ((secComb P.A.hom c b).f i₀) = 0` using `fun k hk => by`. Establish `h` using `mem_filt _ hc k hk`.

Rewrite `h` using `[jetFun_eq hy' hi, hrig]`. Conclude with `(mul_eq_zero.1 h).resolve_left (inv_ne_zero (mul_ne_zero hW1 hρ1))`. Establish `hA : ⊤ ≤ (spMap (epsMap a i) ≫ (epsPt Y i).left) ⁻¹ᵁ MM.L.U (p ⟨⟩)`. Use `top_le_of_surjective (spMap_aug_surjective (R := A) (k := i)) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, spMap_comp_spMap, aug_epsMap, ← spMap_comp_spMap, Category.assoc, aug_epsPt hY]`.

Conclude with `hp`. Establish `e1` using `valR_secMaps ht (A := EpsAlg K i) (epsPt y i).left (top_le_epsPt hy' i hi) (top_le_epsPt hy' i hp0)`. Establish `e2` using `valR_secPull t φ (A := EpsAlg K i) (epsPt y i).left p (top_le_epsPt hy' i hp0)`. Establish `e3 : valR (A` using `EpsAlg K i) ((epsPt y i).left ≫ φ) _ (t.f (p ⟨⟩)) = epsMap j i (valR (spMap (epsMap a i) ≫ (epsPt Y i).left) _ (t.f (p ⟨⟩))) := by`. Rewrite using `[epsPt_pullback hφ hy, ← valR_spMap _ _ _ hA, ← Category.assoc, spMap_comp_spMap, epsMap_comp, hj]`.

Establish `e4` using `topCoeff_mul_valR hy' hi _ hlow (W⁻¹ : (EpsAlg K i)ˣ)`. Use `replace e1 := e1.trans (congrArg (· * _) hW.symm)`. Rewrite `e4` using `[e1, Units.inv_mul_cancel_left, e2, e3, topCoeff_epsMap, map_units_inv]`. Use `⟨(ρ⁻¹ : Aˣ) * topCoeff A i (valR (spMap (epsMap a i) ≫ (epsPt Y i).left) _ (t.f (p ⟨⟩))), ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, e4, map_units_inv, jetFun_eq hy' hi, hrig, mul_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem jetFun_mem_range (hφ : IsGrpPullback P.A AA (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) {r : ℕ}
    {b : Fin r → (lbPow P.L N).Sec} {i₀ : (lbPow P.L N).ι} {y : epsR K ⟶ P.A} {Y : epsR (𝓞 K) ⟶ AA} {c : Fin r → K}
    {t : MM.L.Sec} {i : ℕ} (hi : ⊤ ≤ eSec P.A ⁻¹ᵁ (lbPow P.L N).U i₀) (hY : IsTangent Y)
    (hy : IsVecOver (algebraMap (𝓞 K) K) φ Y y) (ht : SecMaps w (secPull t φ) (secComb P.A.hom c b))
    (hc : c ∈ filt (jetFun y i₀ (rigVal w i₀) b) i) {A : Type} [CommRing A] (a : 𝓞 K →+* A) (j : A →+* K)
    (hj : j.comp a = algebraMap (𝓞 K) K) (p : PUnit.{1} → MM.L.ι)
    (hp : ⊤ ≤ (spMap a ≫ (show Sp (𝓞 K) ⟶ AA.left from eSec AA)) ⁻¹ᵁ MM.L.U (p ⟨⟩)) :
    jetFun y i₀ (rigVal w i₀) b i c ∈ j.range := by
  letI := P.isAb.comm
  have hy' := hy.isTangent hφ hY
  have hja : spMap j ≫ spMap a = spMap (algebraMap (𝓞 K) K) := by rw [spMap_comp_spMap, hj]
  have hpa := (top_le_pull_iff MM.L (eSec AA) (spMap a) p).2 hp
  have hpK : ⊤ ≤ (spMap (algebraMap (𝓞 K) K)) ⁻¹ᵁ (show (Sp (𝓞 K)).Opens from (MM.L.pull (eSec AA)).U p) := by
    rw [← hja]
    exact top_le_comp hpa _
  have he := PolBaseChange.eSec_comm hφ
  have hp0 : ⊤ ≤ eSec P.A ⁻¹ᵁ (MM.L.pull φ).U p :=
    (top_le_pull_iff MM.L φ (A := K) (eSec P.A) p).2 (by
      have := (top_le_pull_iff MM.L (eSec AA) (spMap (algebraMap (𝓞 K) K)) p).1 hpK
      exact he ▸ this)
  obtain ⟨ρ, hρ⟩ := isUnit_valR (X := Sp (𝓞 K)) (spMap a) _ hpa (MM.rig.s p)
  have hρK : valR (X := Sp (𝓞 K)) (spMap (algebraMap (𝓞 K) K)) _ (MM.rig.s p).val = j ρ := by
    rw [hρ, ← hja]
    exact valR_spMap j _ _ hpa _
  have hiw : ⊤ ≤ eSec P.A ⁻¹ᵁ ((lbPow P.L N).U i₀ ⊓ (MM.L.pull φ).U p) := top_le_inf (A := K) hi hp0
  obtain ⟨W, hW⟩ := isUnit_valR (A := EpsAlg K i) (epsPt y i).left _ (top_le_epsPt hy' i hiw) (w.s (i₀, p))
  have hW0 : aug K i W = valR (X := P.A.left) (eSec P.A) _ (w.s (i₀, p)).val := by
    rw [hW, ← aug_epsPt hy' i]
    exact (valR_spMap (aug K i : EpsAlg K i →+* K) _ _ (top_le_epsPt hy' i hiw) _).symm
  have hrig : rigVal w i₀ = aug K i W * j ρ := by rw [rigVal_eq hφ hw hi p hpK, hρK, hW0]
  have hW1 : aug K i W ≠ 0 := (W.isUnit.map (aug K i)).ne_zero
  have hρ1 : j ρ ≠ 0 := (ρ.isUnit.map j).ne_zero
  have hlow : ∀ k < i, jetVal y k _ ((secComb P.A.hom c b).f i₀) = 0 := fun k hk => by
    have h := mem_filt _ hc k hk
    rw [jetFun_eq hy' hi, hrig] at h
    exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero (mul_ne_zero hW1 hρ1))
  have hA : ⊤ ≤ (spMap (epsMap a i) ≫ (epsPt Y i).left) ⁻¹ᵁ MM.L.U (p ⟨⟩) := by
    refine top_le_of_surjective (spMap_aug_surjective (R := A) (k := i)) ?_
    rw [← Category.assoc, spMap_comp_spMap, aug_epsMap, ← spMap_comp_spMap, Category.assoc, aug_epsPt hY]
    exact hp
  have e1 := valR_secMaps ht (A := EpsAlg K i) (epsPt y i).left (top_le_epsPt hy' i hi) (top_le_epsPt hy' i hp0)
  have e2 := valR_secPull t φ (A := EpsAlg K i) (epsPt y i).left p (top_le_epsPt hy' i hp0)
  have e3 : valR (A := EpsAlg K i) ((epsPt y i).left ≫ φ) _ (t.f (p ⟨⟩)) =
      epsMap j i (valR (spMap (epsMap a i) ≫ (epsPt Y i).left) _ (t.f (p ⟨⟩))) := by
    rw [epsPt_pullback hφ hy, ← valR_spMap _ _ _ hA, ← Category.assoc, spMap_comp_spMap, epsMap_comp, hj]
  have e4 := topCoeff_mul_valR hy' hi _ hlow (W⁻¹ : (EpsAlg K i)ˣ)
  replace e1 := e1.trans (congrArg (· * _) hW.symm)
  rw [e1, Units.inv_mul_cancel_left, e2, e3, topCoeff_epsMap, map_units_inv] at e4
  refine ⟨(ρ⁻¹ : Aˣ) * topCoeff A i (valR (spMap (epsMap a i) ≫ (epsPt Y i).left) _ (t.f (p ⟨⟩))), ?_⟩
  rw [map_mul, e4, map_units_inv, jetFun_eq hy' hi, hrig, mul_inv]
  ring

end Model

/- English proof (translation)
Introduce `K _ _ P AA _ _ φ MM N w r b i₀ y Y c t i hM hi hY hy ht hc`. Establish `key : jetFun y i₀ (rigVal w i₀) b i c ∈ (⊥ : Subalgebra (𝓞 K) K)`. Rewrite using `[← MaximalSpectrum.iInf_localization_eq_bot (𝓞 K) K, Algebra.mem_iInf]`. Introduce `v`. Set `A` to `Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors`.

Use `haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A v.asIdeal`. Set `x : Sp A ⟶ AA.left` to `spMap (algebraMap (𝓞 K) A) ≫ (show Sp (𝓞 K) ⟶ AA.left from eSec AA)`. Take `⟨p, hp⟩` from `LB.mem_of_cover MM.isLB (x (IsLocalRing.closedPoint A))`. Establish `hp' : ⊤ ≤ x ⁻¹ᵁ MM.L.U p` using `fun z _ => (IsLocalRing.specializes_closedPoint (R := A) z).mem_open (x ⁻¹ᵁ MM.L.U p).isOpen hp`. Take `⟨z, hz⟩` from `jetFun_mem_range hM.2.2.2.1 hM.2.2.2.2.2.2.1 hi hY hy ht hc (algebraMap (𝓞 K) A) A.val.toRingHom (RingHom.ext fun _ => rfl) (fun _ => p) hp'`.

Conclude with `hz ▸ z.2`. Take `⟨z, hz⟩` from `Algebra.mem_bot.1 key`. Conclude with `hz ▸ z.isIntegral_coe`.
-/
theorem isIntegral_jetFun : ∀ (K'' : Type) [Field K''] [NumberField K''] (P : Out.PolAV (Sp K'')) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (r : ℕ) (b : Fin r → (lbPow P.L N).Sec) (i₀ : (lbPow P.L N).ι) (y : epsR K'' ⟶ P.A) (Y : epsR (𝓞 K'') ⟶ AA) (c : Fin r → K'') (t : MM.L.Sec) (i : ℕ), IsModel w → ⊤ ≤ (eSec P.A) ⁻¹ᵁ (lbPow P.L N).U i₀ → IsTangent Y → GlobalTheory.IsVecOver (algebraMap (𝓞 K'') K'') φ Y y → SecMaps w (secPull t φ) (secComb P.A.hom c b) → c ∈ filt (jetFun y i₀ (rigVal w i₀) b) i → IsIntegral ℤ (jetFun y i₀ (rigVal w i₀) b i c) := by
  intro K _ _ P AA _ _ φ MM N w r b i₀ y Y c t i hM hi hY hy ht hc
  have key : jetFun y i₀ (rigVal w i₀) b i c ∈ (⊥ : Subalgebra (𝓞 K) K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot (𝓞 K) K, Algebra.mem_iInf]
    intro v
    let A := Localization.subalgebra.ofField K v.asIdeal.primeCompl v.asIdeal.primeCompl_le_nonZeroDivisors
    haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A v.asIdeal
    let x : Sp A ⟶ AA.left := spMap (algebraMap (𝓞 K) A) ≫ (show Sp (𝓞 K) ⟶ AA.left from eSec AA)
    obtain ⟨p, hp⟩ := LB.mem_of_cover MM.isLB (x (IsLocalRing.closedPoint A))
    have hp' : ⊤ ≤ x ⁻¹ᵁ MM.L.U p := fun z _ =>
      (IsLocalRing.specializes_closedPoint (R := A) z).mem_open (x ⁻¹ᵁ MM.L.U p).isOpen hp
    obtain ⟨z, hz⟩ := jetFun_mem_range hM.2.2.2.1 hM.2.2.2.2.2.2.1 hi hY hy ht hc (algebraMap (𝓞 K) A)
      A.val.toRingHom (RingHom.ext fun _ => rfl) (fun _ => p) hp'
    exact hz ▸ z.2
  obtain ⟨z, hz⟩ := Algebra.mem_bot.1 key
  exact hz ▸ z.isIntegral_coe

end GlobalTheory.JetIntegral
