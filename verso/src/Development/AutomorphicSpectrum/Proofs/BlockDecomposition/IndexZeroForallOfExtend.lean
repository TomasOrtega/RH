import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltrationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCohomologyOfFrameStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRestrictionCocycleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelationStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.LocGrInd

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def fc {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j q : ℕ} {r : ℤ}
    (hr : r = j + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) : CH.Cn (gr Fil r) j :=
  fun s => sqMk (Fil r) (Fil (r + 1)) (E.form σ I x s) (by
    subst hr
    have := GlobalTheory.T.frame_form_respects_filtration hF E σ j q I x hx s
    simpa using this)

def fs {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j q : ℕ} {r : ℤ}
    (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) : CH.Cn (gr Fil r) j :=
  ∑ I : Idx j d, fc hF E σ hr I.1 (x I) (hx I)

/- English proof (translation)
Rewrite using `[map_sum]`. Unfold `fs`. Rewrite using `[Finset.sum_apply]`. Conclude with `(map_sum (sqM (Fil r) (Fil (r + 1)) (s.obj (Fin.last j))).subtype _ _).trans rfl`.
-/
theorem fs_val {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j q : ℕ} {r : ℤ}
    (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) (s : ComposableArrows C j) :
    (show sqM _ _ _ from fs hF E σ hr x hx s).1 = Ideal.Quotient.mk _ (∑ I : Idx j d, E.form σ I.1 (x I) s) := by
  rw [map_sum]
  unfold fs
  rw [Finset.sum_apply]
  exact (map_sum (sqM (Fil r) (Fil (r + 1)) (s.obj (Fin.last j))).subtype _ _).trans rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl, hv⟩`. Establish `e : f = fs hF E σ hr x hx` using `funext fun s => Subtype.ext ((hv s).trans (fs_val hF E σ hr x hx s).symm)`. Substitute `e` using the available equality. Conclude with `⟨hf, rfl⟩`.

Introduce and unpack `⟨h, rfl⟩`. Conclude with `⟨_, h, rfl, fs_val hF E σ hr x hx⟩`.
-/
theorem rep_iff {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j q : ℕ} {r : ℤ}
    (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) (c : CH.H (gr Fil r) j) :
    Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) c ↔
      ∃ h : CH.d (gr Fil r) j (fs hF E σ hr x hx) = 0, c = (CH.cx (gr Fil r)).cls _ h := by
  constructor
  · rintro ⟨f, hf, rfl, hv⟩
    have e : f = fs hF E σ hr x hx := funext fun s => Subtype.ext ((hv s).trans (fs_val hF E σ hr x hx s).symm)
    subst e
    exact ⟨hf, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, h, rfl, fs_val hF E σ hr x hx⟩

section Cut
variable {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (Fil : ℤ → IdF Φ.A)

abbrev Fil1 : ℤ → IdF (Cut.Φ1 E).A := fun r => (Fil r).res (Cut.U E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (r : ℤ) : gr (Fil1 E Fil) r = Cut.U E ⋙ gr Fil r := rfl

abbrev G (r : ℤ) : C ⥤ ModuleCat.{0} R := Cut.Pσ Q σ ⋙ Cut.U E ⋙ gr Fil r

def jW (r : ℤ) : gr Fil r ⟶ G Q E σ Fil r := Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem jW_eq (r : ℤ) : CH.Mor.ofNatTrans (jW Q E σ Fil r) = CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r)) := rfl

/- English proof (translation)
Establish `cb : ∀ r', Q.Crit Fil (r' + 1) → Q.Crit (fun r => Fil (r + 1)) r'`. Introduce `r' h T b`. Use `(h T b).trans (forall_congr' fun k => ?_)` and prove the remaining obligations. Establish `e : r' + 1 - (k : ℤ) = r' - k + 1` using `by ring`. Rewrite using `[e]`.

Take `⟨β, i, e, s, f⟩` from `GlobalTheory.T.filtration_critical_comparison_map Q E Fil (fun r => Fil (r + 1)) r (fun r' T => hF.anti (by omega) T) h1 h0 (cb _ h2) (cb _ (by simpa using h1))`. Conclude with `⟨Functor.whiskerLeft (Pt.Sσ σ) β, fun T => i _, fun T => e _, fun T => s _, fun T c c' z z' h h' h'' => f ((Pt.Sσ σ).obj T) c c' z z' h h' h''⟩`.
-/
theorem ses (hF : IsFil Φ Fil) (r : ℤ) (h0 : Q.Crit Fil (r - 1)) (h1 : Q.Crit Fil r) (h2 : Q.Crit Fil (r + 1)) :
    ∃ β : G Q E σ Fil r ⟶ G Q E σ Fil (r - 1),
      (∀ T, Function.Injective ((jW Q E σ Fil r).app T).hom) ∧
      (∀ T, Function.Exact ((jW Q E σ Fil r).app T).hom (β.app T).hom) ∧
      (∀ T, Function.Surjective (β.app T).hom) ∧
      ∀ (T : C) (c c' : ℕ →₀ Φ.A.obj T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P T)) (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        (β.app T).hom z = z' := by
  have cb : ∀ r', Q.Crit Fil (r' + 1) → Q.Crit (fun r => Fil (r + 1)) r' := by
    intro r' h T b
    refine (h T b).trans (forall_congr' fun k => ?_)
    have e : r' + 1 - (k : ℤ) = r' - k + 1 := by ring
    rw [e]
  obtain ⟨β, i, e, s, f⟩ := GlobalTheory.T.filtration_critical_comparison_map Q E Fil (fun r => Fil (r + 1)) r (fun r' T => hF.anti (by omega) T) h1 h0 (cb _ h2) (cb _ (by simpa using h1))
  exact ⟨Functor.whiskerLeft (Pt.Sσ σ) β, fun T => i _, fun T => e _, fun T => s _, fun T c c' z z' h h' h'' => f ((Pt.Sσ σ).obj T) c c' z z' h h' h''⟩

abbrev Jm (r : ℤ) : CH.Mor (gr Fil r) (G Q E σ Fil r) (RingHom.id R) := CH.Mor.ofNatTrans (jW Q E σ Fil r)

abbrev Pm (r : ℤ) : CH.Mor (Cut.U E ⋙ gr Fil r) (G Q E σ Fil r) (RingHom.id R) := CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)

variable {Fil}

def cfs (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    CH.Cn (Cut.U E ⋙ gr Fil r) j :=
  fs (Cut.isFil_1 hF) (Cut.E1 E) Cut.can hr x hx

def fsS (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    CH.Cn (gr Fil r) j :=
  ∑ I : Idx j d, fc hF E σ hr (Fin.succ ∘ I.1) (x I) (hx I)

def fsZ (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    CH.Cn (gr Fil r) (j + 1) :=
  ∑ I : Idx j d, fc hF E σ hr (Fin.cons 0 (Fin.succ ∘ I.1)) (x I) (hx I)

/- English proof (translation)
Unfold `cfs fsS fs`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.T.frame_form_restriction_cocycle Q hF E σ hc j q r hr I.1 (x I) (hx I) _ _ (fun s => rfl) (fun s => rfl)`.
-/
theorem pull_cfs (hF : IsFil Φ Fil) (hc : E.GrConst Fil) {j q : ℕ} {r : ℤ} (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D)
    (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    (Pm Q E σ Fil r).pullC j (cfs E hF hr x hx) = (Jm Q E σ Fil r).pullC j (fsS E σ hF hr x hx) := by
  unfold cfs fsS fs
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  exact GlobalTheory.T.frame_form_restriction_cocycle Q hF E σ hc j q r hr I.1 (x I) (hx I) _ _ (fun s => rfl) (fun s => rfl)

/- English proof (translation)
Establish `h1 : Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j))))) ∈ (Fil ((1 : ℕ) : ℤ)).S (Q.P (s.obj (Fin.last j)))`. Establish `: (Fil ((1 : ℕ) : ℤ)).S (Q.P (s.obj (Fin.last j))) = Φ.J.S _` using `by simpa using hF.one _`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))`. Establish `h2` using `(Fil _).map_mem (Q.j (s.obj (Fin.last j))) (GlobalTheory.T.frame_form_respects_filtration hF E σ j q I x hx s)`.

Establish `h3` using `hF.mul 1 (j + q) _ h1 h2`. Establish `e : (((1 + (j + q) : ℕ)) : ℤ) = r` using `by subst hr; push_cast; ring`. Rewrite `h3` using `[e]`. Then use the resulting hypothesis.
-/
theorem mem_y (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (I : Fin j → Fin (d + 1)) (x : Φ.A.obj E.D)
    (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C j) :
    (Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j)))))) *
      (Φ.A.map (Q.j _)).hom (E.form σ I x s) ∈ (Fil r).S (Q.P (s.obj (Fin.last j))) := by
  have h1 : Q.X (s.obj (Fin.last j)) + (Φ.A.map (Q.j _)).hom (E.a σ 0 (s.map (homOfLE (Fin.zero_le (Fin.last j))))) ∈
      (Fil ((1 : ℕ) : ℤ)).S (Q.P (s.obj (Fin.last j))) := by
    have : (Fil ((1 : ℕ) : ℤ)).S (Q.P (s.obj (Fin.last j))) = Φ.J.S _ := by simpa using hF.one _
    rw [this]
    exact Ideal.add_mem _ (Q.X_mem _) (Φ.J.map_mem _ (E.mem 0 _ _))
  have h2 := (Fil _).map_mem (Q.j (s.obj (Fin.last j))) (GlobalTheory.T.frame_form_respects_filtration hF E σ j q I x hx s)
  have h3 := hF.mul 1 (j + q) _ h1 h2
  have e : (((1 + (j + q) : ℕ)) : ℤ) = r := by subst hr; push_cast; ring
  rwa [e] at h3

def yc (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (I : Fin j → Fin (d + 1)) (x : Φ.A.obj E.D)
    (hx : x ∈ (Fil q).S E.D) : CH.Cn (G Q E σ Fil r) j :=
  fun s => sqMk (Fil r) (Fil (r + 1)) _ (mem_y Q E σ hF hr I x hx s)

/- English proof (translation)
The claim follows from `GlobalTheory.T.frame_form_coboundary_relation Q hF E σ hc j q r (by rw [hr]; push_cast; ring) I x hx _ _ (fun s => rfl) (fun s => rfl)`.
-/
theorem d_yc (hF : IsFil Φ Fil) (hc : E.GrConst Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (hx : x ∈ (Fil q).S E.D) :
    CH.d _ j (yc Q E σ hF hr (Fin.succ ∘ I) x hx) =
      -(Jm Q E σ Fil r).pullC (j + 1) (fc hF E σ hr (Fin.cons 0 (Fin.succ ∘ I)) x hx) :=
  GlobalTheory.T.frame_form_coboundary_relation Q hF E σ hc j q r (by rw [hr]; push_cast; ring) I x hx _ _ (fun s => rfl) (fun s => rfl)

/- English proof (translation)
The claim follows from `GlobalTheory.T.frame_form_restriction_cocycle Q hF E σ hc j q r hr I x hx _ _ (fun s => rfl) (fun s => rfl)`.
-/
theorem pull_fc (hF : IsFil Φ Fil) (hc : E.GrConst Fil) {j q : ℕ} {r : ℤ} (hr : r = j + q) (I : Fin j → Fin d) (x : Φ.A.obj E.D)
    (hx : x ∈ (Fil q).S E.D) :
    (Pm Q E σ Fil r).pullC j (fc (Cut.isFil_1 hF) (Cut.E1 E) Cut.can hr I x hx) =
      (Jm Q E σ Fil r).pullC j (fc hF E σ hr (Fin.succ ∘ I) x hx) :=
  GlobalTheory.T.frame_form_restriction_cocycle Q hF E σ hc j q r hr I x hx _ _ (fun s => rfl) (fun s => rfl)

/- English proof (translation)
Establish `d0` using `Φ.dp_zero (Q.X_mem T)`. Establish `d1` using `Φ.dp_one (Q.X_mem T)`. Use `hβ T (Finsupp.single 0 (a * u) + Finsupp.single 1 u) (Finsupp.single 0 u) z z' ?_ ?_ ?_` and prove the remaining obligations. Introduce `k`. Consider the cases of `k with`.

Consider the case `zero => simp`. Consider the case `succ k => simp`. Rewrite using `[hz, Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]), Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), d0, d1]`. Use `congrArg _ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hz', Finsupp.sum_single_index (by simp), d0, mul_one]`.
-/
theorem beta_val (hF : IsFil Φ Fil) {r : ℤ} (β : G Q E σ Fil r ⟶ G Q E σ Fil (r - 1))
    (hβ : ∀ (T : C) (c c' : ℕ →₀ Φ.A.obj T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P T)) (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        (β.app T).hom z = z')
    (T : C) (a u : Φ.A.obj T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P T)) (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P T))
    (hz : z.1 = Ideal.Quotient.mk _ ((Q.X T + (Φ.A.map (Q.j T)).hom a) * (Φ.A.map (Q.j T)).hom u))
    (hz' : z'.1 = Ideal.Quotient.mk _ ((Φ.A.map (Q.j T)).hom u)) : (β.app T).hom z = z' := by
  have d0 := Φ.dp_zero (Q.X_mem T)
  have d1 := Φ.dp_one (Q.X_mem T)
  refine hβ T (Finsupp.single 0 (a * u) + Finsupp.single 1 u) (Finsupp.single 0 u) z z' ?_ ?_ ?_
  · intro k
    cases k with
    | zero => simp
    | succ k => simp
  · rw [hz, Finsupp.sum_add_index' (by simp) (by intros; simp [add_mul]), Finsupp.sum_single_index (by simp),
      Finsupp.sum_single_index (by simp), d0, d1]
    refine congrArg _ ?_
    rw [map_mul]
    ring
  · rw [hz', Finsupp.sum_single_index (by simp), d0, mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Conclude with `beta_val Q E σ hF β hβ _ _ _ _ _ rfl rfl`.
-/
theorem beta_yc (hF : IsFil Φ Fil) {r : ℤ} (β : G Q E σ Fil r ⟶ G Q E σ Fil (r - 1))
    (hβ : ∀ (T : C) (c c' : ℕ →₀ Φ.A.obj T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P T)) (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        (β.app T).hom z = z')
    {j q : ℕ} (hr : r = (j + 1 : ℕ) + q) (hr' : r - 1 = j + q) (I : Fin j → Fin (d + 1)) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) :
    (CH.Mor.ofNatTrans β).pullC j (yc Q E σ hF hr I x hx) =
      (Jm Q E σ Fil (r - 1)).pullC j (fc hF E σ hr' I x hx) := by
  funext s
  exact beta_val Q E σ hF β hβ _ _ _ _ _ rfl rfl

end Cut

section Idx
variable {j d : ℕ}

def idxS (I : Idx j d) : Idx j (d + 1) := ⟨Fin.succ ∘ I.1, (Fin.strictMono_succ).comp I.2⟩

/- English proof (translation)
Introduce `a b hab`. Proceed by induction on `a using Fin.cases with`. Consider the case `zero`. Proceed by induction on `b using Fin.cases with`. Consider the case `zero => exact absurd hab (lt_irrefl _)`.

Consider the case `succ b => simpa using Fin.succ_pos _`. Consider the case `succ a`. Proceed by induction on `b using Fin.cases with`. Consider the case `zero => exact absurd hab (Fin.not_lt_zero _)`. Consider the case `succ b => simpa using I.2 (Fin.succ_lt_succ_iff.1 hab)`.
-/
theorem cons_mono (I : Idx j d) : StrictMono (Fin.cons 0 (Fin.succ ∘ I.1) : Fin (j + 1) → Fin (d + 1)) := by
  intro a b hab
  induction a using Fin.cases with
  | zero =>
    induction b using Fin.cases with
    | zero => exact absurd hab (lt_irrefl _)
    | succ b => simpa using Fin.succ_pos _
  | succ a =>
    induction b using Fin.cases with
    | zero => exact absurd hab (Fin.not_lt_zero _)
    | succ b => simpa using I.2 (Fin.succ_lt_succ_iff.1 hab)

def idxZ (I : Idx j d) : Idx (j + 1) (d + 1) := ⟨Fin.cons 0 (Fin.succ ∘ I.1), cons_mono I⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `(a | a) (b | b) h`. Use `congrArg Sum.inl (Subtype.ext (funext fun k => Fin.succ_injective _ (congrFun (congrArg Subtype.val h) k)))` and prove the remaining obligations. Use `congrFun (congrArg Subtype.val h) 0` as an intermediate fact. Simplify using `[idxS, idxZ] at this`.

Use `congrFun (congrArg Subtype.val h) 0` as an intermediate fact. Simplify using `[idxS, idxZ] at this`. Conclude with `absurd this.symm (Fin.succ_ne_zero _)`. Use `congrArg Sum.inr (Subtype.ext (funext fun k => Fin.succ_injective _ ?_))` and prove the remaining obligations. Simplify `congrFun (congrArg Subtype.val h) k.succ` using `[idxZ]`.

Introduce `I`. Distinguish the cases in `h : I.1 0 = 0`. Establish `ne : ∀ k : Fin j, I.1 k.succ ≠ 0` using `fun k e => by`. Use `I.2 (Fin.succ_pos k)` as an intermediate fact. Rewrite `this` using `[h, e]`.

Conclude with `lt_irrefl _ this`. Use `⟨Sum.inr ⟨fun k => (I.1 k.succ).pred (ne k), fun a b hab => ?_⟩, Subtype.ext (funext fun k => ?_)⟩` and prove the remaining obligations. Conclude with `Fin.pred_lt_pred_iff.2 (I.2 (Fin.succ_lt_succ_iff.2 hab))`. Proceed by induction on `k using Fin.cases with`. Consider the case `zero => simpa [idxZ] using h.symm`.

Consider the case `succ k => simp [idxZ]`. Establish `ne : ∀ k : Fin (j + 1), I.1 k ≠ 0` using `fun k e => by`. Use `I.2.monotone (Fin.zero_le k)` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `h (Fin.le_zero_iff.1 this)`.

Use `⟨Sum.inl ⟨fun k => (I.1 k).pred (ne k), fun a b hab => ?_⟩, Subtype.ext (funext fun k => ?_)⟩` and prove the remaining obligations. Conclude with `Fin.pred_lt_pred_iff.2 (I.2 hab)`. Simplify using `[idxS]`.
-/
theorem idx_bij : Function.Bijective (Sum.elim idxS idxZ : Idx (j + 1) d ⊕ Idx j d → Idx (j + 1) (d + 1)) := by
  constructor
  · rintro (a | a) (b | b) h
    · refine congrArg Sum.inl (Subtype.ext (funext fun k => Fin.succ_injective _ (congrFun (congrArg Subtype.val h) k)))
    · have := congrFun (congrArg Subtype.val h) 0
      simp [idxS, idxZ] at this
    · have := congrFun (congrArg Subtype.val h) 0
      simp [idxS, idxZ] at this
      exact absurd this.symm (Fin.succ_ne_zero _)
    · refine congrArg Sum.inr (Subtype.ext (funext fun k => Fin.succ_injective _ ?_))
      simpa [idxZ] using congrFun (congrArg Subtype.val h) k.succ
  · intro I
    by_cases h : I.1 0 = 0
    · have ne : ∀ k : Fin j, I.1 k.succ ≠ 0 := fun k e => by
        have := I.2 (Fin.succ_pos k)
        rw [h, e] at this
        exact lt_irrefl _ this
      refine ⟨Sum.inr ⟨fun k => (I.1 k.succ).pred (ne k), fun a b hab => ?_⟩, Subtype.ext (funext fun k => ?_)⟩
      · exact Fin.pred_lt_pred_iff.2 (I.2 (Fin.succ_lt_succ_iff.2 hab))
      · induction k using Fin.cases with
        | zero => simpa [idxZ] using h.symm
        | succ k => simp [idxZ]
    · have ne : ∀ k : Fin (j + 1), I.1 k ≠ 0 := fun k e => by
        have := I.2.monotone (Fin.zero_le k)
        rw [e] at this
        exact h (Fin.le_zero_iff.1 this)
      refine ⟨Sum.inl ⟨fun k => (I.1 k).pred (ne k), fun a b hab => ?_⟩, Subtype.ext (funext fun k => ?_)⟩
      · exact Fin.pred_lt_pred_iff.2 (I.2 hab)
      · simp [idxS]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b _ => Subtype.ext (funext fun k => k.elim0), fun b => ⟨⟨fun k => k.elim0, fun a => a.elim0⟩, Subtype.ext (funext fun k => k.elim0)⟩⟩`.
-/
theorem index_zero_extend_bij : Function.Bijective (idxS : Idx 0 d → Idx 0 (d + 1)) :=
  ⟨fun a b _ => Subtype.ext (funext fun k => k.elim0),
    fun b => ⟨⟨fun k => k.elim0, fun a => a.elim0⟩, Subtype.ext (funext fun k => k.elim0)⟩⟩

/- English proof (translation)
Rewrite using `[← Fintype.sum_bijective _ idx_bij (fun z => F (Sum.elim idxS idxZ z)) F (fun _ => rfl), Fintype.sum_sum_type]`. Both sides reduce to the same expression.
-/
theorem sum_idx {M : Type*} [AddCommMonoid M] (F : Idx (j + 1) (d + 1) → M) :
    ∑ I, F I = ∑ I, F (idxS I) + ∑ I, F (idxZ I) := by
  rw [← Fintype.sum_bijective _ idx_bij (fun z => F (Sum.elim idxS idxZ z)) F (fun _ => rfl), Fintype.sum_sum_type]
  rfl

end Idx

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem cls_congr {K : Cx.{1} R} {n : ℕ} {a b : K.X n} (e : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst e; rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `rfl : j = 0 := by`. Assume the negation of the conclusion as `h`. Conclude with `(I.1 ⟨0, by omega⟩).elim0`. Use function extensionality and compare the values at `s`. Establish `v : ∀ i : Fin 2, (Φ.A.map (GlobalTheory.CatH.toLast i s)).hom (E.form σ I.1 x (GlobalTheory.CatH.face i s)) = (Φ.A.map (σ (s.obj (Fin.last 1)))).hom x`.

Introduce `i`. Simplify using `only [Frame.form, Finset.univ_eq_empty, Finset.prod_empty, one_mul]`. Rewrite using `[← Cut.mapA_comp, E.ext' (σ := _ ≫ GlobalTheory.CatH.toLast i s) (σ' := σ (s.obj (Fin.last 1))) (fun i => i.elim0)]`. Establish `t : ((gr Fil r).map (GlobalTheory.CatH.toLast 0 s)).hom (fc hF E σ hr I.1 x hx (GlobalTheory.CatH.face 0 s)) = ((gr Fil r).map (GlobalTheory.CatH.toLast 1 s)).hom (fc hF E σ hr I.1 x hx (GlobalTheory.CatH.face 1 s))` using `Subtype.ext (show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ from congrArg _ ((v 0).trans (v 1).symm))`. Express the relevant statement in the definitionally equal form `∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((gr Fil r).map (GlobalTheory.CatH.toLast i s)).hom (fc hF E σ hr I.1 x hx (GlobalTheory.CatH.face i s)) = 0`.

Rewrite using `[Fin.sum_univ_two]`. Express the relevant statement in the definitionally equal form `(-1 : ℤ) ^ 0 • _ + (-1 : ℤ) ^ 1 • _ = (0 : _)`. Rewrite using `[t]`. Simplify using the standard rewrite rules.
-/
theorem cyc0 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ 0) (σ : ∀ T : C, E.D ⟶ T) {j q : ℕ} {r : ℤ} (hr : r = j + q)
    (I : Idx j 0) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) : CH.d (gr Fil r) j (fc hF E σ hr I.1 x hx) = 0 := by
  obtain rfl : j = 0 := by
    by_contra h
    exact (I.1 ⟨0, by omega⟩).elim0
  funext s
  have v : ∀ i : Fin 2, (Φ.A.map (GlobalTheory.CatH.toLast i s)).hom (E.form σ I.1 x (GlobalTheory.CatH.face i s)) =
      (Φ.A.map (σ (s.obj (Fin.last 1)))).hom x := by
    intro i
    simp only [Frame.form, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    rw [← Cut.mapA_comp, E.ext' (σ := _ ≫ GlobalTheory.CatH.toLast i s) (σ' := σ (s.obj (Fin.last 1))) (fun i => i.elim0)]
  have t : ((gr Fil r).map (GlobalTheory.CatH.toLast 0 s)).hom (fc hF E σ hr I.1 x hx (GlobalTheory.CatH.face 0 s)) =
      ((gr Fil r).map (GlobalTheory.CatH.toLast 1 s)).hom (fc hF E σ hr I.1 x hx (GlobalTheory.CatH.face 1 s)) :=
    Subtype.ext (show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ from congrArg _ ((v 0).trans (v 1).symm))
  change ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • ((gr Fil r).map (GlobalTheory.CatH.toLast i s)).hom (fc hF E σ hr I.1 x hx (GlobalTheory.CatH.face i s)) = 0
  rw [Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • _ + (-1 : ℤ) ^ 1 • _ = (0 : _)
  rw [t]
  simp

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `R _ C _ Φ Q Fil hF E σ hc r hQ j q hr I x hx`. Conclude with `cyc0 hF E σ hr I x hx`.

Consider the case `succ d ih`. Introduce `R _ C _ Φ Q Fil hF E σ hc r hQ j q hr I x hx`. Take `⟨β, bi, be, bs, bf⟩` from `ses Q E σ Fil hF r (hQ _ (by omega)) (hQ _ (by omega)) (hQ _ (by omega))`. Take `⟨c1, -, -⟩` from `CrystallineSemistableComparison.P.ses_cochains (jW Q E σ Fil r) β bi be bs`. Establish `caseS : ∀ {j q : ℕ} (hr : r = j + q) (I : Idx j d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D), CH.d (gr Fil r) j (fc hF E σ hr (idxS I).1 x hx) = 0`.

Introduce `j q hr I x hx`. Establish `h` using `ih (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) hr I x hx`. Apply `c1 (j + 1)` to reduce the goal to its premises. Rewrite using `[map_zero]`. Express the relevant statement in the definitionally equal form `(Jm Q E σ Fil r).pullC (j + 1) (CH.d _ j _) = 0`.

Rewrite using `[← CH.Mor.d_pullC]`. Use `(congrArg (CH.d _ j) (pull_fc Q E σ hF hc hr I.1 x hx).symm).trans ?_` and prove the remaining obligations. Rewrite using `[CH.Mor.d_pullC]`. Conclude with `(congrArg ((Pm Q E σ Fil r).pullC (j + 1)) h).trans (map_zero _)`. Establish `caseZ : ∀ {j q : ℕ} (hr : r = (j + 1 : ℕ) + q) (I : Idx j d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D), CH.d (gr Fil r) (j + 1) (fc hF E σ hr (idxZ I).1 x hx) = 0`.

Introduce `j q hr I x hx`. Apply `c1 (j + 2)` to reduce the goal to its premises. Rewrite using `[map_zero]`. Express the relevant statement in the definitionally equal form `(Jm Q E σ Fil r).pullC (j + 2) (CH.d _ (j + 1) _) = 0`. Rewrite using `[← CH.Mor.d_pullC]`.

Establish `e : (Jm Q E σ Fil r).pullC (j + 1) (fc hF E σ hr (idxZ I).1 x hx) = -CH.d _ j (yc Q E σ hF hr (Fin.succ ∘ I.1) x hx)`. Rewrite using `[d_yc Q E σ hF hc hr I.1 x hx, neg_neg]`. Both sides reduce to the same expression. Rewrite using `[e, map_neg, CH.d_d, neg_zero]`. Consider the cases of `j with`.

Consider the case `zero`. Take `⟨I', rfl⟩` from `index_zero_extend_bij.2 I`. Conclude with `caseS hr I' x hx`. Consider the case `succ n`. Take `⟨z, rfl⟩` from `idx_bij.2 I`.

Break down `z with I' | I'` into its components or cases. Conclude with `caseS hr I' x hx`. Conclude with `caseZ hr I' x hx`.
-/
theorem cyc : ∀ (d : ℕ) {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (r : ℤ)
    (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ} (hr : r = j + q) (I : Idx j d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D),
    CH.d (gr Fil r) j (fc hF E σ hr I.1 x hx) = 0 := by
  intro d
  induction d with
  | zero =>
    intro R _ C _ Φ Q Fil hF E σ hc r hQ j q hr I x hx
    exact cyc0 hF E σ hr I x hx
  | succ d ih =>
    intro R _ C _ Φ Q Fil hF E σ hc r hQ j q hr I x hx
    obtain ⟨β, bi, be, bs, bf⟩ := ses Q E σ Fil hF r (hQ _ (by omega)) (hQ _ (by omega)) (hQ _ (by omega))
    obtain ⟨c1, -, -⟩ := CrystallineSemistableComparison.P.ses_cochains (jW Q E σ Fil r) β bi be bs
    have caseS : ∀ {j q : ℕ} (hr : r = j + q) (I : Idx j d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D),
        CH.d (gr Fil r) j (fc hF E σ hr (idxS I).1 x hx) = 0 := by
      intro j q hr I x hx
      have h := ih (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r
        (fun r' h => Cut.criterion_truncation Q (hQ r' h)) hr I x hx
      apply c1 (j + 1)
      rw [map_zero]
      change (Jm Q E σ Fil r).pullC (j + 1) (CH.d _ j _) = 0
      rw [← CH.Mor.d_pullC]
      refine (congrArg (CH.d _ j) (pull_fc Q E σ hF hc hr I.1 x hx).symm).trans ?_
      rw [CH.Mor.d_pullC]
      exact (congrArg ((Pm Q E σ Fil r).pullC (j + 1)) h).trans (map_zero _)
    have caseZ : ∀ {j q : ℕ} (hr : r = (j + 1 : ℕ) + q) (I : Idx j d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D),
        CH.d (gr Fil r) (j + 1) (fc hF E σ hr (idxZ I).1 x hx) = 0 := by
      intro j q hr I x hx
      apply c1 (j + 2)
      rw [map_zero]
      change (Jm Q E σ Fil r).pullC (j + 2) (CH.d _ (j + 1) _) = 0
      rw [← CH.Mor.d_pullC]
      have e : (Jm Q E σ Fil r).pullC (j + 1) (fc hF E σ hr (idxZ I).1 x hx) = -CH.d _ j (yc Q E σ hF hr (Fin.succ ∘ I.1) x hx) := by
        rw [d_yc Q E σ hF hc hr I.1 x hx, neg_neg]
        rfl
      rw [e, map_neg, CH.d_d, neg_zero]
    cases j with
    | zero =>
      obtain ⟨I', rfl⟩ := index_zero_extend_bij.2 I
      exact caseS hr I' x hx
    | succ n =>
      obtain ⟨z, rfl⟩ := idx_bij.2 I
      rcases z with I' | I'
      · exact caseS hr I' x hx
      · exact caseZ hr I' x hx

/- English proof (translation)
Unfold `fs`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun I _ => cyc d Q hF E σ hc r hQ hr I _ _`.
-/
theorem d_fs {d : ℕ} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ} (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D)
    (hx : ∀ I, x I ∈ (Fil q).S E.D) : CH.d (gr Fil r) j (fs hF E σ hr x hx) = 0 := by
  unfold fs
  rw [map_sum]
  exact Finset.sum_eq_zero fun I _ => cyc d Q hF E σ hc r hQ hr I _ _

section Cut2
variable {d : ℕ} (Q : Poly Φ) (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) {Fil : ℤ → IdF Φ.A}

/- English proof (translation)
The claim follows from `d_fs (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) hr x hx`.
-/
theorem d_cfs (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ} (hr : r = j + q)
    (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) : CH.d _ j (cfs E hF hr x hx) = 0 :=
  d_fs (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) hr x hx

/- English proof (translation)
Unfold `fsS`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun I _ => cyc (d + 1) Q hF E σ hc r hQ hr (idxS I) _ _`.
-/
theorem d_fsS (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ} (hr : r = j + q)
    (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) : CH.d _ j (fsS E σ hF hr x hx) = 0 := by
  unfold fsS
  rw [map_sum]
  exact Finset.sum_eq_zero fun I _ => cyc (d + 1) Q hF E σ hc r hQ hr (idxS I) _ _

/- English proof (translation)
Unfold `fsZ`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun I _ => cyc (d + 1) Q hF E σ hc r hQ hr (idxZ I) _ _`.
-/
theorem d_fsZ (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ} (hr : r = (j + 1 : ℕ) + q)
    (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) : CH.d _ (j + 1) (fsZ E σ hF hr x hx) = 0 := by
  unfold fsZ
  rw [map_sum]
  exact Finset.sum_eq_zero fun I _ => cyc (d + 1) Q hF E σ hc r hQ hr (idxZ I) _ _

/- English proof (translation)
The claim follows from `sum_idx _`.
-/
theorem fs_split (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (x : Idx (j + 1) (d + 1) → Φ.A.obj E.D)
    (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    fs hF E σ hr x hx = fsS E σ hF hr (x ∘ idxS) (fun I => hx _) + fsZ E σ hF hr (x ∘ idxZ) (fun I => hx _) :=
  sum_idx _

/- English proof (translation)
The claim follows from `(Fintype.sum_bijective _ index_zero_extend_bij _ _ fun _ => rfl).symm`.
-/
theorem fs_split0 (hF : IsFil Φ Fil) {q : ℕ} {r : ℤ} (hr : r = (0 : ℕ) + q) (x : Idx 0 (d + 1) → Φ.A.obj E.D)
    (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    fs hF E σ hr x hx = fsS E σ hF hr (x ∘ idxS) (fun I => hx _) :=
  (Fintype.sum_bijective _ index_zero_extend_bij _ _ fun _ => rfl).symm

def ys (hF : IsFil Φ Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (x : Idx j d → Φ.A.obj E.D)
    (hx : ∀ I, x I ∈ (Fil q).S E.D) : CH.Cn (G Q E σ Fil r) j :=
  ∑ I : Idx j d, yc Q E σ hF hr (Fin.succ ∘ I.1) (x I) (hx I)

/- English proof (translation)
Unfold `ys fsZ`. Rewrite using `[map_sum, map_neg, map_sum, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun I _ => d_yc Q E σ hF hc hr I.1 (x I) (hx I)`.
-/
theorem d_ys (hF : IsFil Φ Fil) (hc : E.GrConst Fil) {j q : ℕ} {r : ℤ} (hr : r = (j + 1 : ℕ) + q) (x : Idx j d → Φ.A.obj E.D)
    (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    CH.d _ j (ys Q E σ hF hr x hx) = (Jm Q E σ Fil r).pullC (j + 1) (-fsZ E σ hF hr x hx) := by
  unfold ys fsZ
  rw [map_sum, map_neg, map_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun I _ => d_yc Q E σ hF hc hr I.1 (x I) (hx I)

/- English proof (translation)
Unfold `ys fsS`. Rewrite using `[map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun I _ => beta_yc Q E σ hF β hβ hr hr' _ _ _`.
-/
theorem beta_ys (hF : IsFil Φ Fil) {r : ℤ} (β : G Q E σ Fil r ⟶ G Q E σ Fil (r - 1))
    (hβ : ∀ (T : C) (c c' : ℕ →₀ Φ.A.obj T) (z : sqM (Fil r) (Fil (r + 1)) (Q.P T)) (z' : sqM (Fil (r - 1)) (Fil (r - 1 + 1)) (Q.P T)),
        (∀ k, c' k = c (k + 1)) →
        z.1 = Ideal.Quotient.mk _ (c.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        z'.1 = Ideal.Quotient.mk _ (c'.sum fun k y => (Φ.A.map (Q.j T)).hom y * Φ.dp k (Q.X T)) →
        (β.app T).hom z = z')
    {j q : ℕ} (hr : r = (j + 1 : ℕ) + q) (hr' : r - 1 = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    (CH.Mor.ofNatTrans β).pullC j (ys Q E σ hF hr x hx) = (Jm Q E σ Fil (r - 1)).pullC j (fsS E σ hF hr' x hx) := by
  unfold ys fsS
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun I _ => beta_yc Q E σ hF β hβ hr hr' _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `s`. Use `Subtype.ext ((Ideal.Quotient.eq_zero_iff_mem).2 ?_)` and prove the remaining obligations. Establish `h' : x ∈ (Fil ((q + 1 : ℕ) : ℤ)).S E.D` using `by simpa using h`. Use `GlobalTheory.T.frame_form_respects_filtration hF E σ j (q + 1) I x h' s` as an intermediate fact. Establish `e : ((j + (q + 1) : ℕ) : ℤ) = r + 1` using `by subst hr; push_cast; ring`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem fc_zero (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {j q : ℕ} {r : ℤ} (hr : r = j + q) (I : Fin j → Fin d)
    (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (h : x ∈ (Fil ((q : ℤ) + 1)).S E.D) : fc hF E σ hr I x hx = 0 := by
  funext s
  refine Subtype.ext ((Ideal.Quotient.eq_zero_iff_mem).2 ?_)
  have h' : x ∈ (Fil ((q + 1 : ℕ) : ℤ)).S E.D := by simpa using h
  have := GlobalTheory.T.frame_form_respects_filtration hF E σ j (q + 1) I x h' s
  have e : ((j + (q + 1) : ℕ) : ℤ) = r + 1 := by subst hr; push_cast; ring
  rwa [e] at this

def St (d : ℕ) : Prop :=
  ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (r : ℤ)
    (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D

/- English proof (translation)
The claim follows from `CrystallineSemistableComparison.P.adj _ _ _ (Cut.adjPσ Q σ) n`.
-/
theorem adjB (Fil : ℤ → IdF Φ.A) (r : ℤ) (n : ℕ) : Function.Bijective ((Pm Q E σ Fil r).pull n) :=
  CrystallineSemistableComparison.P.adj _ _ _ (Cut.adjPσ Q σ) n

/- English proof (translation)
The claim follows from `cls_congr (pull_cfs Q E σ hF hc hr x hx) _ _`.
-/
theorem pull_cls (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ} (hr : r = j + q)
    (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D) :
    (Pm Q E σ Fil r).pull j ((CH.cx _).cls _ (d_cfs Q E hF hc r hQ hr x hx)) =
      (Jm Q E σ Fil r).pull j ((CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr x hx)) :=
  cls_congr (pull_cfs Q E σ hF hc hr x hx) _ _

/- English proof (translation)
Use `(IH (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) j).1 h` as an intermediate fact. Establish `h2 : Subsingleton (CH.H (Cut.U E ⋙ gr Fil r) j)` using `this`. Conclude with `(adjB Q E σ Fil r j).2.subsingleton`.
-/
theorem cut_sub (IH : St d) (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') (j : ℕ)
    (h : r < j) : Subsingleton (CH.H (G Q E σ Fil r) j) := by
  have := (IH (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) j).1 h
  have h2 : Subsingleton (CH.H (Cut.U E ⋙ gr Fil r) j) := this
  exact (adjB Q E σ Fil r j).2.subsingleton

/- English proof (translation)
Take `⟨c, rfl⟩` from `(adjB Q E σ Fil r j).2 h`. Take `⟨x, hx, hp⟩` from `((IH (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) j).2 q hr).1 c`. Take `⟨h1, rfl⟩` from `(rep_iff (Cut.isFil_1 hF) (Cut.E1 E) Cut.can hr x hx c).1 hp`. Conclude with `⟨x, hx, pull_cls Q E σ hF hc r hQ hr x hx⟩`.
-/
theorem cut_rep (IH : St d) (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ}
    (hr : r = j + q) (h : CH.H (G Q E σ Fil r) j) :
    ∃ (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D),
      h = (Jm Q E σ Fil r).pull j ((CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr x hx)) := by
  obtain ⟨c, rfl⟩ := (adjB Q E σ Fil r j).2 h
  obtain ⟨x, hx, hp⟩ := ((IH (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r
    (fun r' h => Cut.criterion_truncation Q (hQ r' h)) j).2 q hr).1 c
  obtain ⟨h1, rfl⟩ := (rep_iff (Cut.isFil_1 hF) (Cut.E1 E) Cut.can hr x hx c).1 hp
  exact ⟨x, hx, pull_cls Q E σ hF hc r hQ hr x hx⟩

/- English proof (translation)
Rewrite `h` using `[← pull_cls Q E σ hF hc r hQ hr x hx]`. Establish `h0` using `(adjB Q E σ Fil r j).1 (h.trans (map_zero _).symm)`. Conclude with `((IH (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r (fun r' h => Cut.criterion_truncation Q (hQ r' h)) j).2 q hr).2 x hx ((rep_iff (Cut.isFil_1 hF) (Cut.E1 E) Cut.can hr x hx _).2 ⟨d_cfs Q E hF hc r hQ hr x hx, h0.symm⟩)`.
-/
theorem cut_zero (IH : St d) (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (r : ℤ) (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') {j q : ℕ}
    (hr : r = j + q) (x : Idx j d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D)
    (h : (Jm Q E σ Fil r).pull j ((CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr x hx)) = 0) :
    ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  rw [← pull_cls Q E σ hF hc r hQ hr x hx] at h
  have h0 := (adjB Q E σ Fil r j).1 (h.trans (map_zero _).symm)
  exact ((IH (Cut.Q1 Q) (Cut.isFil_1 hF) (Cut.E1 E) Cut.can (Cut.grConst_1 hc) r
    (fun r' h => Cut.criterion_truncation Q (hQ r' h)) j).2 q hr).2 x hx
    ((rep_iff (Cut.isFil_1 hF) (Cut.E1 E) Cut.can hr x hx _).2 ⟨d_cfs Q E hF hc r hQ hr x hx, h0.symm⟩)

end Cut2

section Glue
variable {j d : ℕ} {α : Type*}

/- English proof (translation)
Set `e` to `Equiv.ofBijective _ (idx_bij (j := j) (d := d))`. Use `⟨fun I => Sum.elim xs xz (e.symm I), funext fun I => ?_, funext fun I => ?_⟩` and prove the remaining obligations. Establish `: e.symm (idxS I) = Sum.inl I` using `e.symm_apply_apply (Sum.inl I)`. Simplify using `only [Function.comp, this, Sum.elim_inl]`. Establish `: e.symm (idxZ I) = Sum.inr I` using `e.symm_apply_apply (Sum.inr I)`.

Simplify using `only [Function.comp, this, Sum.elim_inr]`.
-/
theorem glue (xs : Idx (j + 1) d → α) (xz : Idx j d → α) : ∃ x : Idx (j + 1) (d + 1) → α, x ∘ idxS = xs ∧ x ∘ idxZ = xz := by
  let e := Equiv.ofBijective _ (idx_bij (j := j) (d := d))
  refine ⟨fun I => Sum.elim xs xz (e.symm I), funext fun I => ?_, funext fun I => ?_⟩
  · have : e.symm (idxS I) = Sum.inl I := e.symm_apply_apply (Sum.inl I)
    simp only [Function.comp, this, Sum.elim_inl]
  · have : e.symm (idxZ I) = Sum.inr I := e.symm_apply_apply (Sum.inr I)
    simp only [Function.comp, this, Sum.elim_inr]

/- English proof (translation)
Set `e` to `Equiv.ofBijective _ (index_zero_extend_bij (d := d))`. Use `⟨fun I => xs (e.symm I), funext fun I => ?_⟩` and prove the remaining obligations. Establish `: e.symm (idxS I) = I` using `e.symm_apply_apply I`. Simplify using `only [Function.comp, this]`.
-/
theorem glue0 (xs : Idx 0 d → α) : ∃ x : Idx 0 (d + 1) → α, x ∘ idxS = xs := by
  let e := Equiv.ofBijective _ (index_zero_extend_bij (d := d))
  refine ⟨fun I => xs (e.symm I), funext fun I => ?_⟩
  have : e.symm (idxS I) = I := e.symm_apply_apply I
  simp only [Function.comp, this]

/- English proof (translation)
Take `⟨z, rfl⟩` from `idx_bij.2 I`. Break down `z with I' | I'` into its components or cases. Conclude with `h1 I'`. Conclude with `h2 I'`.
-/
theorem idx_all {P : Idx (j + 1) (d + 1) → Prop} (h1 : ∀ I, P (idxS I)) (h2 : ∀ I, P (idxZ I)) (I) : P I := by
  obtain ⟨z, rfl⟩ := idx_bij.2 I
  rcases z with I' | I'
  · exact h1 I'
  · exact h2 I'

/- English proof (translation)
Take `⟨I', rfl⟩` from `index_zero_extend_bij.2 I`. Conclude with `h1 I'`.
-/
theorem index_zero_forall_of_extend {P : Idx 0 (d + 1) → Prop} (h1 : ∀ I, P (idxS I)) (I) : P I := by
  obtain ⟨I', rfl⟩ := index_zero_extend_bij.2 I
  exact h1 I'

end Glue

/- English proof (translation)
Introduce `R _ C _ Φ Q Fil hF E σ hc r hQ j`. Establish `hQ1 : ∀ r' ≤ r - 1 + 1, Q.Crit Fil r'` using `fun r' h => hQ r' (by omega)`. Take `⟨β, bi, be, bs, bf⟩` from `ses Q E σ Fil hF r (hQ _ (by omega)) (hQ _ (by omega)) (hQ _ (by omega))`. Take `⟨c1, c2, c3⟩` from `CrystallineSemistableComparison.P.ses_cochains (jW Q E σ Fil r) β bi be bs`. Take `⟨δ, hδ, i0, e1, e2, e3⟩` from `CrystallineSemistableComparison.P.les (Jm Q E σ Fil r).hom (CH.Mor.ofNatTrans β).hom c1 c2 c3`.

Establish `D : ∀ {n q : ℕ} (hr : r = (n + 1 : ℕ) + q) (hn : r - 1 = n + q) (x : Idx n d → Φ.A.obj E.D) (hx : ∀ I, x I ∈ (Fil q).S E.D), δ n ((Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn x hx))) = -(CH.cx _).cls _ (d_fsZ Q E σ hF hc r hQ hr x hx)`. Introduce `n q hr hn x hx`. Establish `hZ` using `d_fsZ Q E σ hF hc r hQ hr x hx`. Establish `hnZ : CH.d _ (n + 1) (-fsZ E σ hF hr x hx) = 0` using `by rw [map_neg, hZ, neg_zero]`. Establish `hb` using `beta_ys Q E σ hF β bf hr hn x hx`.

Establish `hz : CH.d _ n ((CH.Mor.ofNatTrans β).hom.f n (ys Q E σ hF hr x hx)) = 0`. Express the relevant statement in the definitionally equal form `CH.d _ n ((CH.Mor.ofNatTrans β).pullC n _) = 0`. Rewrite using `[hb, CH.Mor.d_pullC, d_fsS Q E σ hF hc (r - 1) hQ1 hn x hx, map_zero]`. Establish `h` using `hδ n (ys Q E σ hF hr x hx) (-fsZ E σ hF hr x hx) hz hnZ (d_ys Q E σ hF hc hr x hx).symm`. Establish `e : (Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn x hx)) = (CH.cx _).cls _ hz` using `cls_congr hb.symm _ _`.

Rewrite using `[e, h]`. Both sides reduce to the same expression. Establish `Dinj : ∀ {n q : ℕ} (hr : r = n + q), Function.Injective (δ n)`. Introduce `n q hr`. Use `(injective_iff_map_eq_zero _).2 fun z hz => ?_` and prove the remaining obligations.

Take `⟨w, rfl⟩` from `(e2 n z).1 hz`. Take `⟨x, hx, e⟩` from `cut_rep Q E σ IH hF hc r hQ hr w`. Rewrite using `[e]`. Conclude with `(e1 n _).2 ⟨_, rfl⟩`. Use `⟨fun h => ?_, fun q hr => ⟨fun c => ?_, fun x hx hrep => ?_⟩⟩` and prove the remaining obligations.

Consider the cases of `j with`. Consider the case `zero`. Use `cut_sub Q E σ IH hF hc r hQ 0 h` as an intermediate fact. Conclude with `⟨fun a b => i0 (Subsingleton.elim _ _)⟩`. Consider the case `succ n`.

Establish `s1` using `cut_sub Q E σ IH hF hc r hQ (n + 1) h`. Establish `s2` using `cut_sub Q E σ IH hF hc (r - 1) hQ1 n (by push_cast at h; omega)`. Establish `key : ∀ c : CH.H (gr Fil r) (n + 1), c = 0` using `fun c => by`. Take `⟨z, rfl⟩` from `(e3 n c).1 (Subsingleton.elim _ _)`. Rewrite using `[Subsingleton.elim z 0, map_zero]`.

Conclude with `⟨fun a b => (key a).trans (key b).symm⟩`. Consider the cases of `j with`. Consider the case `zero`. Take `⟨x, hx, e⟩` from `cut_rep Q E σ IH hF hc r hQ hr ((Jm Q E σ Fil r).pull 0 c)`. Take `⟨x', rfl⟩` from `glue0 x`.

Establish `hx' : ∀ I, x' I ∈ (Fil q).S E.D` using `index_zero_forall_of_extend (P := fun I => x' I ∈ (Fil q).S E.D) hx`. Use `⟨x', hx', (rep_iff hF E σ hr x' hx' c).2 ⟨d_fs Q hF E σ hc r hQ hr x' hx', ?_⟩⟩` and prove the remaining obligations. Conclude with `(i0 e).trans (cls_congr (fs_split0 E σ hF hr x' hx').symm _ _)`. Consider the case `succ n`. Establish `hn : r - 1 = n + q` using `by rw [hr]; push_cast; ring`.

Take `⟨xs, hxs, e⟩` from `cut_rep Q E σ IH hF hc r hQ hr ((Jm Q E σ Fil r).pull (n + 1) c)`. Establish `h0 : (Jm Q E σ Fil r).hom.mapH (n + 1) (c - (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr xs hxs)) = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.2 e`. Take `⟨z, hz⟩` from `(e3 n _).1 h0`.

Take `⟨xz, hxz, ez⟩` from `cut_rep Q E σ IH hF hc (r - 1) hQ1 hn (-z)`. Establish `hd` using `D hr hn xz hxz`. Rewrite `hd` using `[← ez, map_neg, hz]`. Establish `hc'` using `sub_eq_iff_eq_add'.1 (neg_inj.1 hd)`. Take `⟨x', rfl, rfl⟩` from `glue xs xz`.

Establish `hx' : ∀ I, x' I ∈ (Fil q).S E.D` using `idx_all (P := fun I => x' I ∈ (Fil q).S E.D) hxs hxz`. Use `⟨x', hx', (rep_iff hF E σ hr x' hx' c).2 ⟨d_fs Q hF E σ hc r hQ hr x' hx', ?_⟩⟩` and prove the remaining obligations. Conclude with `hc'.trans ((CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ _ _ (by rw [map_add, d_fsS Q E σ hF hc r hQ hr _ hxs, d_fsZ Q E σ hF hc r hQ hr _ hxz, add_zero])).symm.trans (cls_congr (fs_split E σ hF hr x' hx').symm _ _))`. Take `⟨h, h0⟩` from `(rep_iff hF E σ hr x hx 0).1 hrep`. Consider the cases of `j with`.

Consider the case `zero`. Establish `hxs : ∀ I, (x ∘ idxS) I ∈ (Fil q).S E.D` using `fun I => hx _`. Establish `e0 : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) = 0` using `(cls_congr (fs_split0 E σ hF hr x hx).symm _ _).trans h0.symm`. Use `cut_zero Q E σ IH hF hc r hQ hr (x ∘ idxS) hxs (by rw [e0]; exact map_zero _)` as an intermediate fact. Conclude with `index_zero_forall_of_extend (P := fun I => x I ∈ (Fil ((q : ℤ) + 1)).S E.D) this`.

Consider the case `succ n`. Establish `hn : r - 1 = n + q` using `by rw [hr]; push_cast; ring`. Establish `hxs : ∀ I, (x ∘ idxS) I ∈ (Fil q).S E.D` using `fun I => hx _`. Establish `hxz : ∀ I, (x ∘ idxZ) I ∈ (Fil q).S E.D` using `fun I => hx _`. Establish `e0 : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) + (CH.cx _).cls _ (d_fsZ Q E σ hF hc r hQ hr (x ∘ idxZ) hxz) = 0` using `((CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ _ _ (by rw [map_add, d_fsS Q E σ hF hc r hQ hr _ hxs, d_fsZ Q E σ hF hc r hQ hr _ hxz, add_zero])).symm.trans (cls_congr (fs_split E σ hF hr x hx).symm _ _)).trans h0.symm`.

Establish `hd` using `D hr hn (x ∘ idxZ) hxz`. Establish `e1' : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) = δ n ((Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn (x ∘ idxZ) hxz)))`. Rewrite using `[hd]`. Conclude with `eq_neg_of_add_eq_zero_left e0`. Establish `hJ : (Jm Q E σ Fil r).pull (n + 1) ((CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs)) = 0`.

Rewrite using `[e1']`. Conclude with `(e3 n _).2 ⟨_, rfl⟩`. Establish `hs` using `cut_zero Q E σ IH hF hc r hQ hr (x ∘ idxS) hxs hJ`. Establish `hS0 : fsS E σ hF hr (x ∘ idxS) hxs = 0` using `Finset.sum_eq_zero fun I _ => fc_zero hF E σ hr _ _ _ (hs I)`. Establish `c0 : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) = 0` using `(cls_congr hS0 _ (map_zero _)).trans rfl`.

Establish `hz0` using `Dinj (n := n) (q := q + 1) (by rw [hr]; push_cast; ring) (by rw [← e1', c0, map_zero] : δ n ((Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn (x ∘ idxZ) hxz))) = δ n 0)`. Establish `hz'` using `cut_zero Q E σ IH hF hc (r - 1) hQ1 hn (x ∘ idxZ) hxz hz0`. Conclude with `idx_all (P := fun I => x I ∈ (Fil ((q : ℤ) + 1)).S E.D) hs hz'`.
-/
theorem step {d : ℕ} (IH : St d) : St (d + 1) := by
  intro R _ C _ Φ Q Fil hF E σ hc r hQ j
  have hQ1 : ∀ r' ≤ r - 1 + 1, Q.Crit Fil r' := fun r' h => hQ r' (by omega)
  obtain ⟨β, bi, be, bs, bf⟩ := ses Q E σ Fil hF r (hQ _ (by omega)) (hQ _ (by omega)) (hQ _ (by omega))
  obtain ⟨c1, c2, c3⟩ := CrystallineSemistableComparison.P.ses_cochains (jW Q E σ Fil r) β bi be bs
  obtain ⟨δ, hδ, i0, e1, e2, e3⟩ := CrystallineSemistableComparison.P.les (Jm Q E σ Fil r).hom (CH.Mor.ofNatTrans β).hom c1 c2 c3
  have D : ∀ {n q : ℕ} (hr : r = (n + 1 : ℕ) + q) (hn : r - 1 = n + q) (x : Idx n d → Φ.A.obj E.D)
      (hx : ∀ I, x I ∈ (Fil q).S E.D),
      δ n ((Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn x hx))) =
        -(CH.cx _).cls _ (d_fsZ Q E σ hF hc r hQ hr x hx) := by
    intro n q hr hn x hx
    have hZ := d_fsZ Q E σ hF hc r hQ hr x hx
    have hnZ : CH.d _ (n + 1) (-fsZ E σ hF hr x hx) = 0 := by rw [map_neg, hZ, neg_zero]
    have hb := beta_ys Q E σ hF β bf hr hn x hx
    have hz : CH.d _ n ((CH.Mor.ofNatTrans β).hom.f n (ys Q E σ hF hr x hx)) = 0 := by
      change CH.d _ n ((CH.Mor.ofNatTrans β).pullC n _) = 0
      rw [hb, CH.Mor.d_pullC, d_fsS Q E σ hF hc (r - 1) hQ1 hn x hx, map_zero]
    have h := hδ n (ys Q E σ hF hr x hx) (-fsZ E σ hF hr x hx) hz hnZ (d_ys Q E σ hF hc hr x hx).symm
    have e : (Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn x hx)) =
        (CH.cx _).cls _ hz := cls_congr hb.symm _ _
    rw [e, h]
    rfl
  have Dinj : ∀ {n q : ℕ} (hr : r = n + q), Function.Injective (δ n) := by
    intro n q hr
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    obtain ⟨w, rfl⟩ := (e2 n z).1 hz
    obtain ⟨x, hx, e⟩ := cut_rep Q E σ IH hF hc r hQ hr w
    rw [e]
    exact (e1 n _).2 ⟨_, rfl⟩
  refine ⟨fun h => ?_, fun q hr => ⟨fun c => ?_, fun x hx hrep => ?_⟩⟩
  · cases j with
    | zero =>
      have := cut_sub Q E σ IH hF hc r hQ 0 h
      exact ⟨fun a b => i0 (Subsingleton.elim _ _)⟩
    | succ n =>
      have s1 := cut_sub Q E σ IH hF hc r hQ (n + 1) h
      have s2 := cut_sub Q E σ IH hF hc (r - 1) hQ1 n (by push_cast at h; omega)
      have key : ∀ c : CH.H (gr Fil r) (n + 1), c = 0 := fun c => by
        obtain ⟨z, rfl⟩ := (e3 n c).1 (Subsingleton.elim _ _)
        rw [Subsingleton.elim z 0, map_zero]
      exact ⟨fun a b => (key a).trans (key b).symm⟩
  · cases j with
    | zero =>
      obtain ⟨x, hx, e⟩ := cut_rep Q E σ IH hF hc r hQ hr ((Jm Q E σ Fil r).pull 0 c)
      obtain ⟨x', rfl⟩ := glue0 x
      have hx' : ∀ I, x' I ∈ (Fil q).S E.D := index_zero_forall_of_extend (P := fun I => x' I ∈ (Fil q).S E.D) hx
      refine ⟨x', hx', (rep_iff hF E σ hr x' hx' c).2 ⟨d_fs Q hF E σ hc r hQ hr x' hx', ?_⟩⟩
      exact (i0 e).trans (cls_congr (fs_split0 E σ hF hr x' hx').symm _ _)
    | succ n =>
      have hn : r - 1 = n + q := by rw [hr]; push_cast; ring
      obtain ⟨xs, hxs, e⟩ := cut_rep Q E σ IH hF hc r hQ hr ((Jm Q E σ Fil r).pull (n + 1) c)
      have h0 : (Jm Q E σ Fil r).hom.mapH (n + 1) (c - (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr xs hxs)) = 0 := by
        rw [map_sub]
        exact sub_eq_zero.2 e
      obtain ⟨z, hz⟩ := (e3 n _).1 h0
      obtain ⟨xz, hxz, ez⟩ := cut_rep Q E σ IH hF hc (r - 1) hQ1 hn (-z)
      have hd := D hr hn xz hxz
      rw [← ez, map_neg, hz] at hd
      have hc' := sub_eq_iff_eq_add'.1 (neg_inj.1 hd)
      obtain ⟨x', rfl, rfl⟩ := glue xs xz
      have hx' : ∀ I, x' I ∈ (Fil q).S E.D := idx_all (P := fun I => x' I ∈ (Fil q).S E.D) hxs hxz
      refine ⟨x', hx', (rep_iff hF E σ hr x' hx' c).2 ⟨d_fs Q hF E σ hc r hQ hr x' hx', ?_⟩⟩
      exact hc'.trans ((CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ _ _ (by rw [map_add, d_fsS Q E σ hF hc r hQ hr _ hxs, d_fsZ Q E σ hF hc r hQ hr _ hxz, add_zero])).symm.trans
        (cls_congr (fs_split E σ hF hr x' hx').symm _ _))
  · obtain ⟨h, h0⟩ := (rep_iff hF E σ hr x hx 0).1 hrep
    cases j with
    | zero =>
      have hxs : ∀ I, (x ∘ idxS) I ∈ (Fil q).S E.D := fun I => hx _
      have e0 : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) = 0 :=
        (cls_congr (fs_split0 E σ hF hr x hx).symm _ _).trans h0.symm
      have := cut_zero Q E σ IH hF hc r hQ hr (x ∘ idxS) hxs (by rw [e0]; exact map_zero _)
      exact index_zero_forall_of_extend (P := fun I => x I ∈ (Fil ((q : ℤ) + 1)).S E.D) this
    | succ n =>
      have hn : r - 1 = n + q := by rw [hr]; push_cast; ring
      have hxs : ∀ I, (x ∘ idxS) I ∈ (Fil q).S E.D := fun I => hx _
      have hxz : ∀ I, (x ∘ idxZ) I ∈ (Fil q).S E.D := fun I => hx _
      have e0 : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) +
          (CH.cx _).cls _ (d_fsZ Q E σ hF hc r hQ hr (x ∘ idxZ) hxz) = 0 :=
        ((CrystallineSemistableComparison.CechClassBoundaries.cls_add _ _ _ _ (by rw [map_add, d_fsS Q E σ hF hc r hQ hr _ hxs, d_fsZ Q E σ hF hc r hQ hr _ hxz, add_zero])).symm.trans
          (cls_congr (fs_split E σ hF hr x hx).symm _ _)).trans h0.symm
      have hd := D hr hn (x ∘ idxZ) hxz
      have e1' : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) =
          δ n ((Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn (x ∘ idxZ) hxz))) := by
        rw [hd]
        exact eq_neg_of_add_eq_zero_left e0
      have hJ : (Jm Q E σ Fil r).pull (n + 1) ((CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs)) = 0 := by
        rw [e1']
        exact (e3 n _).2 ⟨_, rfl⟩
      have hs := cut_zero Q E σ IH hF hc r hQ hr (x ∘ idxS) hxs hJ
      have hS0 : fsS E σ hF hr (x ∘ idxS) hxs = 0 :=
        Finset.sum_eq_zero fun I _ => fc_zero hF E σ hr _ _ _ (hs I)
      have c0 : (CH.cx _).cls _ (d_fsS Q E σ hF hc r hQ hr (x ∘ idxS) hxs) = 0 :=
        (cls_congr hS0 _ (map_zero _)).trans rfl
      have hz0 := Dinj (n := n) (q := q + 1) (by rw [hr]; push_cast; ring) (by rw [← e1', c0, map_zero] :
        δ n ((Jm Q E σ Fil (r - 1)).pull n ((CH.cx _).cls _ (d_fsS Q E σ hF hc (r - 1) hQ1 hn (x ∘ idxZ) hxz))) = δ n 0)
      have hz' := cut_zero Q E σ IH hF hc (r - 1) hQ1 hn (x ∘ idxZ) hxz hz0
      exact idx_all (P := fun I => x I ∈ (Fil ((q : ℤ) + 1)).S E.D) hs hz'

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `R _ C _ Φ Q Fil hF E σ hc r hQ j`. Conclude with `GlobalTheory.T.graded_cohomology_of_frame hF E σ r j`.

Consider the case `succ d ih => exact step ih`.
-/
theorem st : ∀ d, St d := by
  intro d
  induction d with
  | zero =>
    intro R _ C _ Φ Q Fil hF E σ hc r hQ j
    exact GlobalTheory.T.graded_cohomology_of_frame hF E σ r j
  | succ d ih => exact step ih

/- English proof (translation)
Introduce `R _ C _ Φ Q Fil hF d E σ hc r hQ j`. Conclude with `st d Q hF E σ hc r hQ j`.
-/
theorem loc_gr : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (r : ℤ)
    (hQ : ∀ r' ≤ r + 1, Q.Crit Fil r') (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j d → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D :=
  by
  intro R _ C _ Φ Q Fil hF d E σ hc r hQ j
  exact st d Q hF E σ hc r hQ j

end GlobalTheory.CompanionTheory.LocGrInd
