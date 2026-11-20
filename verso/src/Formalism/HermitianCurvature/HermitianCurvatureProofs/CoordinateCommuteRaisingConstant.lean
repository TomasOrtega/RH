import Formalism.HermitianCurvature.StatementMA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerLevelsSameScalar

section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx1

open Formalism.FourierDecayAlt Finset Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

section Defs

variable (P : Par) (D : DAlg P.r)

def lA (Y : ℂ) : A P D :=
  l0A P D Y + ggiA P D * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j

def mA (Y : ℂ) : A P D :=
  m0A P D Y + ggiA P D * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D j)

def fnsA : Set (A P D) :=
  Set.range (cA P D) ∪ Set.range (ciA P D) ∪ Set.range (cbA P D) ∪ Set.range (cbiA P D) ∪
    {zA P D, ziA P D, zbA P D, zbiA P D, ggA P D, ggiA P D}

def zfnsA : Set (A P D) := {zA P D, ziA P D, zbA P D, zbiA P D, ggA P D, ggiA P D}

def sitesFromD (i : ℕ) : List (Site (A P D)) := ((List.ofFn (siteA P D)).drop i).reverse

def QQlev (l i : ℕ) (Y : ℂ) : M2 (A P D) :=
  (((sitesFromD P D i).map fun σ => Ts σ (star Y)).prod)ᴴ * (startM P D l).QQ Y *
    ((sitesFromD P D i).map fun σ => Ts σ Y).prod

/- English proof (translation)
Simplify using `[sites, sitesFromD]`.
-/
theorem sites_eq : sites P D = sitesFromD P D 0 := by
  simp [sites, sitesFromD]

end Defs

def LevFns : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], (∀ x ∈ fnsA P D, ∀ y ∈ fnsA P D, x * y = y * x) ∧
    (∀ l, cA P D l * ciA P D l = 1 ∧ ciA P D l * cA P D l = 1 ∧ cbA P D l * cbiA P D l = 1 ∧ cbiA P D l * cbA P D l = 1) ∧
    zA P D * ziA P D = 1 ∧ ziA P D * zA P D = 1 ∧ zbA P D * zbiA P D = 1 ∧ zbiA P D * zbA P D = 1 ∧
    ggA P D * ggiA P D = 1 ∧ ggiA P D * ggA P D = 1 ∧ ggA P D = zA P D * zbA P D - algebraMap ℂ (A P D) (P.TT : ℂ)

def LevP : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : Fin P.r),
    (∀ m, pA P D l * cA P D m = cA P D m * pA P D l + (if l = m then cA P D m else 0)) ∧
    (∀ m, pA P D l * ciA P D m = ciA P D m * pA P D l - (if l = m then ciA P D m else 0)) ∧
    ∀ x ∈ Set.range (cbA P D) ∪ Set.range (cbiA P D) ∪ zfnsA P D, pA P D l * x = x * pA P D l

def LevPb : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : Fin P.r),
    (∀ m, pbA P D l * cbA P D m = cbA P D m * pbA P D l + (if l = m then cbA P D m else 0)) ∧
    (∀ m, pbA P D l * cbiA P D m = cbiA P D m * pbA P D l - (if l = m then cbiA P D m else 0)) ∧
    ∀ x ∈ Set.range (cA P D) ∪ Set.range (ciA P D) ∪ zfnsA P D, pbA P D l * x = x * pbA P D l

def LevPP : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l m : Fin P.r), pA P D l * pA P D m = pA P D m * pA P D l ∧ pA P D l * pbA P D m = pbA P D m * pA P D l ∧
    pbA P D l * pbA P D m = pbA P D m * pbA P D l ∧ pA P D l * nabA P D = nabA P D * pA P D l ∧
    pbA P D l * nabA P D = nabA P D * pbA P D l ∧ pA P D l * nabsA P D = nabsA P D * pA P D l ∧
    pbA P D l * nabsA P D = nabsA P D * pbA P D l

def LevNab : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], nabA P D * zA P D = zA P D * nabA P D + 1 ∧ nabA P D * ziA P D = ziA P D * nabA P D - ziA P D * ziA P D ∧
    nabA P D * zbA P D = zbA P D * nabA P D ∧ nabA P D * zbiA P D = zbiA P D * nabA P D ∧
    nabA P D * ggA P D = ggA P D * nabA P D + zbA P D ∧
    nabA P D * ggiA P D = ggiA P D * nabA P D - zbA P D * ggiA P D * ggiA P D ∧
    ∀ x ∈ Set.range (cA P D) ∪ Set.range (ciA P D) ∪ Set.range (cbA P D) ∪ Set.range (cbiA P D),
      nabA P D * x = x * nabA P D

def LevNabs : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], nabsA P D * zbA P D = zbA P D * nabsA P D - 1 ∧ nabsA P D * zbiA P D = zbiA P D * nabsA P D + zbiA P D * zbiA P D ∧
    nabsA P D * zA P D = zA P D * nabsA P D ∧ nabsA P D * ziA P D = ziA P D * nabsA P D ∧
    nabsA P D * ggA P D = ggA P D * nabsA P D - zA P D ∧
    nabsA P D * ggiA P D = ggiA P D * nabsA P D + zA P D * ggiA P D * ggiA P D ∧
    ∀ x ∈ Set.range (cA P D) ∪ Set.range (ciA P D) ∪ Set.range (cbA P D) ∪ Set.range (cbiA P D),
      nabsA P D * x = x * nabsA P D

def LevelExists : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], ∃ L : LevelData (A P D) P.r, IsModelLevel P D L

def LevelAssemble : Prop := LevFns → LevP → LevPb → LevPP → LevNab → LevNabs → LevelExists

def StarGens : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], (∀ l, star (cA P D l) = cbA P D l ∧ star (ciA P D l) = cbiA P D l ∧ star (pA P D l) = -pbA P D l) ∧
    star (zA P D) = zbA P D ∧ star (ziA P D) = zbiA P D ∧ star (ggA P D) = ggA P D ∧ star (ggiA P D) = ggiA P D ∧
    star (nabA P D) = nabsA P D

def LevelStar : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (L : LevelData (A P D) P.r), IsModelLevel P D L → IsStarLevel L

def SSScalar : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (w : D.Pr), Commute (SS P D l) (sc P D w)

def SSShift : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (f g : Ty P → ℂ), (∀ π π', Up P l π π' → g π' = f π) →
    kap P D g * SS P D l = SS P D l * kap P D f

def SSNorm : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ l ∈ Icc 1 (P.k - 1),
    star (SS P D l) * SS P D l = (kap P D fun π => ((Nrm P l π : ℝ) : ℂ)) ∧
    SS P D l * star (SS P D l) = kap P D fun π => ((NrmDown P l π : ℝ) : ℂ)

def SSComm : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l →
    SS P D j * SS P D l * (kap P D fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) =
      SS P D l * SS P D j * kap P D fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)

def SSMixed : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l →
    star (SS P D l) * SS P D j = SS P D j * star (SS P D l)

def NabSS : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], ∀ l ∈ Icc 1 (P.k - 1),
    nabA P D * SS P D l = SS P D l * nabA P D - zbA P D * ggiA P D * SS P D l ∧
    nabsA P D * SS P D l = SS P D l * nabsA P D - zA P D * ggiA P D * SS P D l

def Curvature : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], nabsA P D * nabA P D - nabA P D * nabsA P D =
    (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) * ggiA P D * ggiA P D

def QQNormal : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ Y : ℂ, (∀ π, xC P π Y ≠ 0) →
    t21 P D Y = t22 P D Y * lA P D Y ∧ t12 P D Y = t22 P D Y * mA P D Y ∧
    ((∀ π, xC P π (Y + 1) ≠ 0) → t11 P D Y =
      qC P Y • (ggiA P D * kap P D fun π => (xC P π (Y + 1))⁻¹) + t22 P D Y * mA P D Y * lA P D Y) ∧
    (star Y = Y → mA P D Y = star (lA P D (Y - 1)))

def QQHerm : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ Y : ℂ, (QQr P D Y)ᴴ = QQr P D (star Y)

def QQRTTEntries : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ (u v : ℂ) (i j k l : Fin 2),
    (u - v) • (QQr P D u i j * QQr P D v k l - QQr P D v k l * QQr P D u i j) =
      QQr P D u k j * QQr P D v i l - QQr P D v k j * QQr P D u i l

def QQRTT : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → IsRTT (QQr P D)

def QQRTTOfEntries : Prop := QQRTTEntries → QQRTT

def QQDet : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → IsDet (QQr P D) (qC P)

def T21Commute : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ u v : ℂ, Commute (t21 P D u) (t21 P D v)

def QQLeading : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∃ a11 a12 a21 a22 : ℕ → A P D, ∀ Y : ℂ,
    t11 P D Y = Y ^ (P.k + 1) • (1 : A P D) + ∑ i ∈ range (P.k + 1), Y ^ i • a11 i ∧
    t12 P D Y = -(Y ^ P.k • zA P D) + ∑ i ∈ range P.k, Y ^ i • a12 i ∧
    t21 P D Y = -(Y ^ P.k • zbA P D) + ∑ i ∈ range P.k, Y ^ i • a21 i ∧
    t22 P D Y = Y ^ (P.k - 1) • ggA P D + ∑ i ∈ range (P.k - 1), Y ^ i • a22 i

def QQZeta : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ), t21 P D Y * zA P D - zA P D * t21 P D Y = -t22 P D Y ∧
    t11 P D Y * zA P D - zA P D * t11 P D Y = -t12 P D Y ∧ Commute (t12 P D Y) (zA P D) ∧ Commute (t22 P D Y) (zA P D)

def StartIsStart : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ l : ℕ, IsStart (startM P D l).QQ (startM P D l).q

def StartIsStartAssemble : Prop := QQHerm → QQRTT → QQDet → StartIsStart

def StartOK : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ (l : ℕ) (L : LevelData (A P D) P.r), IsModelLevel P D L → IsLevelStart L (startM P D l)

def StartAssemble : Prop := StartIsStart → T21Commute → SSScalar → SSShift → RhoUp → StartOK

def SitesOKM : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ), SitesOK (K := ℂ) (startM P D l).QQ (sitesFromD P D 0)

def ChainM : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ), (∀ Y, QQlev P D l P.r Y = (startM P D l).QQ Y) ∧
    ∀ (i : Fin P.r) (Y : ℂ), QQlev P D l i Y =
      (Ts (siteA P D i) (star Y))ᴴ * QQlev P D l (i + 1) Y * Ts (siteA P D i) Y

def LowerCommutes : Prop :=
  ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (i : Fin P.r), QQCommutes (K := ℂ) (QQlev P D l (i + 1)) (siteA P D i)

def LowerStart : Prop := ∀ (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)], P.OK → ∀ l i : ℕ, i ≤ P.r → IsStart (QQlev P D l i) (qC P)

section Ops

variable {r : ℕ} (D : DAlg r)

/- English proof (translation)
Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp, mul_assoc]`.
-/
theorem mulOp_mul (f g : D.R) : D.mulOp f * D.mulOp g = D.mulOp (f * g) := by
  ext h : 1; simp [DAlg.mulOp, mul_assoc]
/- English proof (translation)
Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp, add_mul]`.
-/
theorem mulOp_add (f g : D.R) : D.mulOp f + D.mulOp g = D.mulOp (f + g) := by
  ext h : 1; simp [DAlg.mulOp, add_mul]
/- English proof (translation)
Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp]`.
-/
theorem mulOp_zero : D.mulOp (0 : D.R) = 0 := by ext h : 1; simp [DAlg.mulOp]
/- English proof (translation)
Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp]`.
-/
theorem mulOp_one : D.mulOp (1 : D.R) = 1 := by ext h : 1; simp [DAlg.mulOp]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `mulOp_mul D f g`. Use `show MulOpposite.op (D.mulOp gb * D.mulOp fb) = MulOpposite.op (D.mulOp (fb * gb))`. Rewrite using `[mulOp_mul, mul_comm]`.
-/
theorem multiplierPair_mul (f fb g gb : D.R) : D.fnP f fb * D.fnP g gb = D.fnP (f * g) (fb * gb) := by
  refine Prod.ext ?_ ?_
  · exact mulOp_mul D f g
  · show MulOpposite.op (D.mulOp gb * D.mulOp fb) = MulOpposite.op (D.mulOp (fb * gb))
    rw [mulOp_mul, mul_comm]
/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Conclude with `mulOp_add D f g`. Use `show MulOpposite.op (D.mulOp fb + D.mulOp gb) = MulOpposite.op (D.mulOp (fb + gb))`. Rewrite using `[mulOp_add]`.
-/
theorem multiplierPair_add (f fb g gb : D.R) : D.fnP f fb + D.fnP g gb = D.fnP (f + g) (fb + gb) := by
  refine Prod.ext ?_ ?_
  · exact mulOp_add D f g
  · show MulOpposite.op (D.mulOp fb + D.mulOp gb) = MulOpposite.op (D.mulOp (fb + gb))
    rw [mulOp_add]
/- English proof (translation)
Use `Prod.ext (mulOp_zero D) ?_` and prove the remaining obligations. Use `show MulOpposite.op (D.mulOp (0 : D.R)) = 0`. Rewrite using `[mulOp_zero]`. Both sides reduce to the same expression.
-/
theorem multiplierPair_zero : D.fnP (0 : D.R) 0 = 0 := by
  refine Prod.ext (mulOp_zero D) ?_
  show MulOpposite.op (D.mulOp (0 : D.R)) = 0
  rw [mulOp_zero]; rfl
/- English proof (translation)
Use `Prod.ext (mulOp_one D) ?_` and prove the remaining obligations. Use `show MulOpposite.op (D.mulOp (1 : D.R)) = 1`. Rewrite using `[mulOp_one]`. Both sides reduce to the same expression.
-/
theorem multiplierPair_one : D.fnP (1 : D.R) 1 = 1 := by
  refine Prod.ext (mulOp_one D) ?_
  show MulOpposite.op (D.mulOp (1 : D.R)) = 1
  rw [mulOp_one]; rfl
/- English proof (translation)
Rewrite using `[neg_eq_iff_add_eq_zero, multiplierPair_add, add_neg_cancel, add_neg_cancel, multiplierPair_zero]`.
-/
theorem multiplierPair_neg (f fb : D.R) : -D.fnP f fb = D.fnP (-f) (-fb) := by
  rw [neg_eq_iff_add_eq_zero, multiplierPair_add, add_neg_cancel, add_neg_cancel, multiplierPair_zero]
/- English proof (translation)
Rewrite using `[multiplierPair_mul, multiplierPair_mul, mul_comm f, mul_comm fb]`.
-/
theorem multiplierPair_comm (f fb g gb : D.R) : D.fnP f fb * D.fnP g gb = D.fnP g gb * D.fnP f fb := by
  rw [multiplierPair_mul, multiplierPair_mul, mul_comm f, mul_comm fb]

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show algebraMap ℂ D.Op a * D.mulOp f = D.mulOp ((a : ℂ) • f)`. Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp]`.

Use `show (algebraMap ℂ D.Opᵐᵒᵖ) (starRingEnd ℂ (a : ℂ)) * MulOpposite.op (D.mulOp fb) = MulOpposite.op (D.mulOp ((a : ℂ) • fb))`. Rewrite using `[Complex.conj_ofReal, ← Algebra.smul_def, ← MulOpposite.op_smul]`. Use `congr 1`. Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp]`.
-/
theorem smul_fnP (a : ℝ) (f fb : D.R) : (a : ℂ) • D.fnP f fb = D.fnP ((a : ℂ) • f) ((a : ℂ) • fb) := by
  rw [Algebra.smul_def]
  refine Prod.ext ?_ ?_
  · show algebraMap ℂ D.Op a * D.mulOp f = D.mulOp ((a : ℂ) • f)
    ext h : 1; simp [DAlg.mulOp]
  · show (algebraMap ℂ D.Opᵐᵒᵖ) (starRingEnd ℂ (a : ℂ)) * MulOpposite.op (D.mulOp fb) =
      MulOpposite.op (D.mulOp ((a : ℂ) • fb))
    rw [Complex.conj_ofReal, ← Algebra.smul_def, ← MulOpposite.op_smul]
    congr 1
    ext h : 1; simp [DAlg.mulOp]

/- English proof (translation)
Use `Prod.ext h1 ?_` and prove the remaining obligations. Use `show MulOpposite.op (Ys * Xs) = MulOpposite.op (Xs * Ys)`. Rewrite using `[h2]`.
-/
theorem mk_comm (X Xs Y Ys : D.Op) (h1 : X * Y = Y * X) (h2 : Xs * Ys = Ys * Xs) :
    D.mkP X Xs * D.mkP Y Ys = D.mkP Y Ys * D.mkP X Xs := by
  refine Prod.ext h1 ?_
  show MulOpposite.op (Ys * Xs) = MulOpposite.op (Xs * Ys)
  rw [h2]

/- English proof (translation)
Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).2) h` as an intermediate fact. Simplify using `[M.vz, M.vzb] at this`.
-/
theorem vz_ne : (M.vz : M.Var r) ≠ M.vzb := by
  intro h; have := congrArg (fun p : M.Var r => (ofLex p).2) h; simp [M.vz, M.vzb] at this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).1) h` as an intermediate fact. Simplify `this` using `[M.vc]`. Introduce and unpack `rfl`.

Both sides reduce to the same expression.
-/
theorem vc_inj (l m : Fin r) : (M.vc l : M.Var r) = M.vc m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : M.Var r => (ofLex p).1) h; simpa [M.vc] using this
  · rintro rfl; rfl
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).1) h` as an intermediate fact. Simplify `this` using `[M.vcb]`. Introduce and unpack `rfl`.

Both sides reduce to the same expression.
-/
theorem vcb_inj (l m : Fin r) : (M.vcb l : M.Var r) = M.vcb m ↔ l = m := by
  constructor
  · intro h; have := congrArg (fun p : M.Var r => (ofLex p).1) h; simpa [M.vcb] using this
  · rintro rfl; rfl
/- English proof (translation)
Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).2) h` as an intermediate fact. Simplify using `[M.vc, M.vcb] at this`.
-/
theorem vc_vcb (l m : Fin r) : (M.vc l : M.Var r) ≠ M.vcb m := by
  intro h; have := congrArg (fun p : M.Var r => (ofLex p).2) h; simp [M.vc, M.vcb] at this
/- English proof (translation)
Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).1) h` as an intermediate fact. Conclude with `(Fin.castSucc_lt_last l).ne this`.
-/
theorem vc_vz (l : Fin r) : (M.vc l : M.Var r) ≠ M.vz := by
  intro h; have := congrArg (fun p : M.Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
/- English proof (translation)
Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).1) h` as an intermediate fact. Conclude with `(Fin.castSucc_lt_last l).ne this`.
-/
theorem vc_vzb (l : Fin r) : (M.vc l : M.Var r) ≠ M.vzb := by
  intro h; have := congrArg (fun p : M.Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
/- English proof (translation)
Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).1) h` as an intermediate fact. Conclude with `(Fin.castSucc_lt_last l).ne this`.
-/
theorem vcb_vz (l : Fin r) : (M.vcb l : M.Var r) ≠ M.vz := by
  intro h; have := congrArg (fun p : M.Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this
/- English proof (translation)
Introduce `h`. Use `congrArg (fun p : M.Var r => (ofLex p).1) h` as an intermediate fact. Conclude with `(Fin.castSucc_lt_last l).ne this`.
-/
theorem vcb_vzb (l : Fin r) : (M.vcb l : M.Var r) ≠ M.vzb := by
  intro h; have := congrArg (fun p : M.Var r => (ofLex p).1) h
  exact (Fin.castSucc_lt_last l).ne this

variable {D} {TT : ℝ} (hL : D.Laws TT)
include hL

/- English proof (translation)
Use extensionality with `g : 1`. Simplify using `only [Module.End.mul_apply, LinearMap.add_apply, DAlg.mulOp, LinearMap.mulLeft_apply]`. Rewrite using `[hL.leibniz, add_comm]`.
-/
theorem eulerMul (v : M.Var r) (f : D.R) : D.ev v * D.mulOp f = D.mulOp f * D.ev v + D.mulOp (D.ev v f) := by
  ext g : 1
  simp only [Module.End.mul_apply, LinearMap.add_apply, DAlg.mulOp, LinearMap.mulLeft_apply]
  rw [hL.leibniz, add_comm]

/- English proof (translation)
Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show D.mulOp a * D.ev v * D.mulOp f = D.mulOp f * (D.mulOp a * D.ev v) + D.mulOp (a * D.ev v f)`. Rewrite using `[mul_assoc, eulerMul hL, mul_add, ← mul_assoc, ← mul_assoc, mulOp_mul, mulOp_mul, mulOp_mul, mul_comm a f]`. Use `show MulOpposite.op (D.mulOp fb * -(D.mulOp b * D.ev w)) = MulOpposite.op (-(D.mulOp b * D.ev w) * D.mulOp fb + D.mulOp (b * D.ev w fb))`. Use `congr 1`.

Rewrite using `[neg_mul, mul_assoc, eulerMul hL, mul_add, ← mul_assoc, mulOp_mul, mulOp_mul, mul_neg, ← mul_assoc, mulOp_mul, mul_comm b fb]`. Normalize the expressions using the abelian group laws.
-/
theorem der_fn (a b : D.R) (v w : M.Var r) (f fb : D.R) :
    D.mkP (D.mulOp a * D.ev v) (-(D.mulOp b * D.ev w)) * D.fnP f fb =
      D.fnP f fb * D.mkP (D.mulOp a * D.ev v) (-(D.mulOp b * D.ev w)) + D.fnP (a * D.ev v f) (b * D.ev w fb) := by
  refine Prod.ext ?_ ?_
  · show D.mulOp a * D.ev v * D.mulOp f = D.mulOp f * (D.mulOp a * D.ev v) + D.mulOp (a * D.ev v f)
    rw [mul_assoc, eulerMul hL, mul_add, ← mul_assoc, ← mul_assoc, mulOp_mul, mulOp_mul, mulOp_mul, mul_comm a f]
  · show MulOpposite.op (D.mulOp fb * -(D.mulOp b * D.ev w)) =
      MulOpposite.op (-(D.mulOp b * D.ev w) * D.mulOp fb + D.mulOp (b * D.ev w fb))
    congr 1
    rw [neg_mul, mul_assoc, eulerMul hL, mul_add, ← mul_assoc, mulOp_mul, mulOp_mul, mul_neg, ← mul_assoc, mulOp_mul,
      mul_comm b fb]
    abel

/- English proof (translation)
Establish `h` using `hL.leibniz v 1 1`. Simplify using `only [mul_one, one_mul] at h`. Take the linear combination `-h`.
-/
theorem ev_one (v : M.Var r) : D.ev v (1 : D.R) = 0 := by
  have h := hL.leibniz v 1 1
  simp only [mul_one, one_mul] at h
  linear_combination -h

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, ev_one hL, smul_zero]`.
-/
theorem ev_const (v : M.Var r) (z : ℂ) : D.ev v (algebraMap ℂ D.R z) = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, ev_one hL, smul_zero]

/- English proof (translation)
The claim follows from `Ring.mul_inverse_cancel f h`.
-/
theorem unit_mul_inv {f : D.R} (h : IsUnit f) : f * D.inv f = 1 := Ring.mul_inverse_cancel f h
/- English proof (translation)
The claim follows from `Ring.inverse_mul_cancel f h`.
-/
theorem unit_inv_mul {f : D.R} (h : IsUnit f) : D.inv f * f = 1 := Ring.inverse_mul_cancel f h

/- English proof (translation)
Establish `h` using `hL.leibniz v f (D.inv f)`. Rewrite `h` using `[unit_mul_inv hL hf, ev_one hL]`. Establish `h1` using `unit_inv_mul hL hf`. Take the linear combination `(-(D.ev v (D.inv f))) * h1 - (D.inv f) * h`.
-/
theorem ev_inv (v : M.Var r) (f : D.R) (hf : IsUnit f) : D.ev v (D.inv f) = -(D.inv f * D.inv f * D.ev v f) := by
  have h := hL.leibniz v f (D.inv f)
  rw [unit_mul_inv hL hf, ev_one hL] at h
  have h1 := unit_inv_mul hL hf
  linear_combination (-(D.ev v (D.inv f))) * h1 - (D.inv f) * h

/- English proof (translation)
The claim follows from `hL.coord v w`.
-/
theorem ec (v w : M.Var r) : D.ev v (D.x w) = if v = w then D.x w else 0 := hL.coord v w

/- English proof (translation)
The claim follows from `hL.unit_alt_bis v`.
-/
theorem ux (v : M.Var r) : IsUnit (D.x v) := hL.unit_alt_bis v

/- English proof (translation)
Rewrite using `[ev_inv hL _ _ (ux hL w), ec hL]`. Use `split_ifs`. Establish `h1` using `unit_inv_mul hL (ux hL w)`. Take the linear combination `(-(D.inv (D.x w))) * h1`. Simplify using the standard rewrite rules.
-/
theorem eci (v w : M.Var r) : D.ev v (D.inv (D.x w)) = if v = w then -(D.inv (D.x w)) else 0 := by
  rw [ev_inv hL _ _ (ux hL w), ec hL]
  split_ifs
  · have h1 := unit_inv_mul hL (ux hL w)
    linear_combination (-(D.inv (D.x w))) * h1
  · simp

/- English proof (translation)
Unfold `DAlg.gg`. Rewrite using `[map_sub, hL.leibniz, ec hL, ec hL, ev_const hL, if_pos rfl, if_neg vz_ne]`. Simplify using the standard rewrite rules.
-/
theorem euler_GG_z : D.ev M.vz (D.gg TT) = D.x M.vz * D.x M.vzb := by
  unfold DAlg.gg
  rw [map_sub, hL.leibniz, ec hL, ec hL, ev_const hL, if_pos rfl, if_neg vz_ne]; simp
/- English proof (translation)
Unfold `DAlg.gg`. Rewrite using `[map_sub, hL.leibniz, ec hL, ec hL, ev_const hL, if_pos rfl, if_neg vz_ne.symm]`. Simplify using the standard rewrite rules.
-/
theorem euler_gg_zb : D.ev M.vzb (D.gg TT) = D.x M.vz * D.x M.vzb := by
  unfold DAlg.gg
  rw [map_sub, hL.leibniz, ec hL, ec hL, ev_const hL, if_pos rfl, if_neg vz_ne.symm]; simp

/- English proof (translation)
Unfold `DAlg.gg`. Rewrite using `[map_sub, hL.leibniz, ec hL, ec hL, ev_const hL, if_neg h1, if_neg h2]`. Simplify using the standard rewrite rules.
-/
theorem euler_gamma_vanish (v : M.Var r) (h1 : v ≠ M.vz) (h2 : v ≠ M.vzb) : D.ev v (D.gg TT) = 0 := by
  unfold DAlg.gg
  rw [map_sub, hL.leibniz, ec hL, ec hL, ev_const hL, if_neg h1, if_neg h2]; simp
/- English proof (translation)
Rewrite using `[ev_inv hL _ _ hL.unit_gg, euler_gamma_vanish hL v h1 h2]`. Simplify using the standard rewrite rules.
-/
theorem euler_gamma_inv_vanish (v : M.Var r) (h1 : v ≠ M.vz) (h2 : v ≠ M.vzb) : D.ev v (D.inv (D.gg TT)) = 0 := by
  rw [ev_inv hL _ _ hL.unit_gg, euler_gamma_vanish hL v h1 h2]; simp

/- English proof (translation)
Rewrite using `[← mul_assoc, eulerMul hL, h, mulOp_zero, add_zero, mul_assoc, mul_assoc, hL.comm]`.
-/
theorem comm_eu (v w : M.Var r) (f : D.R) (h : D.ev v f = 0) :
    D.ev v * (D.mulOp f * D.ev w) = (D.mulOp f * D.ev w) * D.ev v := by
  rw [← mul_assoc, eulerMul hL, h, mulOp_zero, add_zero, mul_assoc, mul_assoc, hL.comm]

/- English proof (translation)
Rewrite using `[multiplierPair_mul, unit_mul_inv hL h, unit_mul_inv hL hb, multiplierPair_one]`.
-/
theorem inv1 (f fb : D.R) (h : IsUnit f) (hb : IsUnit fb) : D.fnP f fb * D.fnP (D.inv f) (D.inv fb) = 1 := by
  rw [multiplierPair_mul, unit_mul_inv hL h, unit_mul_inv hL hb, multiplierPair_one]
/- English proof (translation)
Rewrite using `[multiplierPair_mul, unit_inv_mul hL h, unit_inv_mul hL hb, multiplierPair_one]`.
-/
theorem inv2 (f fb : D.R) (h : IsUnit f) (hb : IsUnit fb) : D.fnP (D.inv f) (D.inv fb) * D.fnP f fb = 1 := by
  rw [multiplierPair_mul, unit_inv_mul hL h, unit_inv_mul hL hb, multiplierPair_one]

end Ops

section Line

variable {r : ℕ} (D : DAlg r)

def nabE (a TT : ℝ) : D.Pr := D.dzP + (a : ℂ) • (D.zbP * D.ggiP TT)

def nabsE (a TT : ℝ) : D.Pr := -D.dzbP + (a : ℂ) • (D.zP * D.ggiP TT)

def ZF (f : D.R) : Prop := ∀ l : Fin r, D.ev (M.vc l) f = 0 ∧ D.ev (M.vcb l) f = 0

def CF (f : D.R) : Prop := D.ev M.vz f = 0 ∧ D.ev M.vzb f = 0

/- English proof (translation)
Rewrite using `[mulOp_one, one_mul, one_mul]`. Both sides reduce to the same expression.
-/
theorem partialDeriv_def (l : Fin r) : D.pP l = D.mkP (D.mulOp 1 * D.ev (M.vc l)) (-(D.mulOp 1 * D.ev (M.vcb l))) := by
  rw [mulOp_one, one_mul, one_mul]; rfl
/- English proof (translation)
Rewrite using `[mulOp_one, one_mul, one_mul]`. Both sides reduce to the same expression.
-/
theorem partialDerivBar_def (l : Fin r) : D.pbP l = D.mkP (D.mulOp 1 * D.ev (M.vcb l)) (-(D.mulOp 1 * D.ev (M.vc l))) := by
  rw [mulOp_one, one_mul, one_mul]; rfl

variable {D} {TT : ℝ} (hL : D.Laws TT)
include hL

/- English proof (translation)
Unfold `nabE`. Rewrite using `[DAlg.zbP, DAlg.ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, DAlg.dzP, der_fn hL]`. Normalize the expressions using the abelian group laws.
-/
theorem nabE_fn (a : ℝ) (f fb : D.R) :
    nabE D a TT * D.fnP f fb = D.fnP f fb * nabE D a TT +
      D.fnP (D.inv (D.x M.vz) * D.ev M.vz f) (D.inv (D.x M.vzb) * D.ev M.vzb fb) := by
  unfold nabE
  rw [DAlg.zbP, DAlg.ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, DAlg.dzP, der_fn hL]
  abel

/- English proof (translation)
Unfold `nabsE`. Rewrite using `[DAlg.zP, DAlg.ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, DAlg.dzbP, neg_mul, der_fn hL, mul_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem nabsE_fn (a : ℝ) (f fb : D.R) :
    nabsE D a TT * D.fnP f fb = D.fnP f fb * nabsE D a TT -
      D.fnP (D.inv (D.x M.vzb) * D.ev M.vzb f) (D.inv (D.x M.vz) * D.ev M.vz fb) := by
  unfold nabsE
  rw [DAlg.zP, DAlg.ggiP, multiplierPair_mul, smul_fnP, add_mul, mul_add, multiplierPair_comm, DAlg.dzbP, neg_mul, der_fn hL, mul_neg]
  abel

/- English proof (translation)
The claim follows from `unit_inv_mul hL (ux hL _)`.
-/
theorem hz : D.inv (D.x M.vz) * D.x M.vz = 1 := unit_inv_mul hL (ux hL _)
/- English proof (translation)
The claim follows from `unit_inv_mul hL (ux hL _)`.
-/
theorem hzb : D.inv (D.x M.vzb) * D.x M.vzb = 1 := unit_inv_mul hL (ux hL _)
/- English proof (translation)
The claim follows from `unit_inv_mul hL hL.unit_gg`.
-/
theorem hgi : D.inv (D.gg TT) * D.gg TT = 1 := unit_inv_mul hL hL.unit_gg

/- English proof (translation)
Rewrite using `[DAlg.zP, nabE_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl, hz hL, hzb hL, multiplierPair_one]`.
-/
theorem nabla_zeta_comm (a : ℝ) : nabE D a TT * D.zP = D.zP * nabE D a TT + 1 := by
  rw [DAlg.zP, nabE_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl, hz hL, hzb hL, multiplierPair_one]
/- English proof (translation)
Rewrite using `[DAlg.ziP, nabE_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]`. Apply the tactic sequence `congr 2 <;> ring`.
-/
theorem nab_zi (a : ℝ) : nabE D a TT * D.ziP = D.ziP * nabE D a TT - D.ziP * D.ziP := by
  rw [DAlg.ziP, nabE_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2 <;> ring
/- English proof (translation)
Rewrite using `[DAlg.zbP, nabE_fn hL, ec hL, ec hL, if_neg vz_ne, if_neg vz_ne.symm]`. Simplify using `only [mul_zero]`. Rewrite using `[multiplierPair_zero, add_zero]`.
-/
theorem nab_zb (a : ℝ) : nabE D a TT * D.zbP = D.zbP * nabE D a TT := by
  rw [DAlg.zbP, nabE_fn hL, ec hL, ec hL, if_neg vz_ne, if_neg vz_ne.symm]
  simp only [mul_zero]
  rw [multiplierPair_zero, add_zero]
/- English proof (translation)
Rewrite using `[DAlg.ggP, nabE_fn hL, euler_GG_z hL, euler_gg_zb hL, DAlg.zbP]`. Use `congr 2`. Take the linear combination `(D.x M.vzb) * hz hL`. Take the linear combination `(D.x M.vz) * hzb hL`.
-/
theorem nab_gg (a : ℝ) : nabE D a TT * D.ggP TT = D.ggP TT * nabE D a TT + D.zbP := by
  rw [DAlg.ggP, nabE_fn hL, euler_GG_z hL, euler_gg_zb hL, DAlg.zbP]
  congr 2
  · linear_combination (D.x M.vzb) * hz hL
  · linear_combination (D.x M.vz) * hzb hL
/- English proof (translation)
Rewrite using `[DAlg.ggiP, nabE_fn hL, ev_inv hL _ _ hL.unit_gg, ev_inv hL _ _ hL.unit_gg, euler_GG_z hL, euler_gg_zb hL, DAlg.zbP, multiplierPair_mul, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]`. Use `congr 2`. Take the linear combination `(-(D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vzb)) * hz hL`. Take the linear combination `(-(D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vz)) * hzb hL`.
-/
theorem nab_ggi (a : ℝ) : nabE D a TT * D.ggiP TT = D.ggiP TT * nabE D a TT - D.zbP * D.ggiP TT * D.ggiP TT := by
  rw [DAlg.ggiP, nabE_fn hL, ev_inv hL _ _ hL.unit_gg, ev_inv hL _ _ hL.unit_gg, euler_GG_z hL, euler_gg_zb hL,
    DAlg.zbP, multiplierPair_mul, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · linear_combination (-(D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vzb)) * hz hL
  · linear_combination (-(D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vz)) * hzb hL
/- English proof (translation)
Rewrite using `[DAlg.zbP, nabsE_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl, hz hL, hzb hL, multiplierPair_one]`.
-/
theorem nabs_zb (a : ℝ) : nabsE D a TT * D.zbP = D.zbP * nabsE D a TT - 1 := by
  rw [DAlg.zbP, nabsE_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl, hz hL, hzb hL, multiplierPair_one]
/- English proof (translation)
Rewrite using `[DAlg.ggP, nabsE_fn hL, euler_GG_z hL, euler_gg_zb hL, DAlg.zP]`. Use `congr 2`. Take the linear combination `(D.x M.vz) * hzb hL`. Take the linear combination `(D.x M.vzb) * hz hL`.
-/
theorem nabs_gg (a : ℝ) : nabsE D a TT * D.ggP TT = D.ggP TT * nabsE D a TT - D.zP := by
  rw [DAlg.ggP, nabsE_fn hL, euler_GG_z hL, euler_gg_zb hL, DAlg.zP]
  congr 2
  · linear_combination (D.x M.vz) * hzb hL
  · linear_combination (D.x M.vzb) * hz hL
/- English proof (translation)
Rewrite using `[DAlg.ggiP, nabsE_fn hL, ev_inv hL _ _ hL.unit_gg, ev_inv hL _ _ hL.unit_gg, euler_GG_z hL, euler_gg_zb hL, DAlg.zP, multiplierPair_mul, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]`. Use `congr 2`. Take the linear combination `(D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vz) * hzb hL`. Take the linear combination `(D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vzb) * hz hL`.
-/
theorem nabs_ggi (a : ℝ) : nabsE D a TT * D.ggiP TT = D.ggiP TT * nabsE D a TT + D.zP * D.ggiP TT * D.ggiP TT := by
  rw [DAlg.ggiP, nabsE_fn hL, ev_inv hL _ _ hL.unit_gg, ev_inv hL _ _ hL.unit_gg, euler_GG_z hL, euler_gg_zb hL,
    DAlg.zP, multiplierPair_mul, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2
  · linear_combination (D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vz) * hzb hL
  · linear_combination (D.inv (D.gg TT) * D.inv (D.gg TT) * D.x M.vzb) * hz hL
/- English proof (translation)
Rewrite using `[DAlg.zbiP, nabsE_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]`. Apply the tactic sequence `congr 2 <;> ring`.
-/
theorem nabs_zbi (a : ℝ) : nabsE D a TT * D.zbiP = D.zbiP * nabsE D a TT + D.zbiP * D.zbiP := by
  rw [DAlg.zbiP, nabsE_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg]
  congr 2 <;> ring
/- English proof (translation)
Rewrite using `[nabE_fn hL, h1, h2, mul_zero, mul_zero, multiplierPair_zero, add_zero]`.
-/
theorem nab_cf (a : ℝ) (f fb : D.R) (h1 : D.ev M.vz f = 0) (h2 : D.ev M.vzb fb = 0) :
    nabE D a TT * D.fnP f fb = D.fnP f fb * nabE D a TT := by
  rw [nabE_fn hL, h1, h2, mul_zero, mul_zero, multiplierPair_zero, add_zero]
/- English proof (translation)
Rewrite using `[nabsE_fn hL, h1, h2, mul_zero, mul_zero, multiplierPair_zero, sub_zero]`.
-/
theorem nabs_cf (a : ℝ) (f fb : D.R) (h1 : D.ev M.vzb f = 0) (h2 : D.ev M.vz fb = 0) :
    nabsE D a TT * D.fnP f fb = D.fnP f fb * nabsE D a TT := by
  rw [nabsE_fn hL, h1, h2, mul_zero, mul_zero, multiplierPair_zero, sub_zero]

/- English proof (translation)
Rewrite using `[partialDeriv_def, DAlg.cP, der_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl, one_mul, one_mul]`.
-/
theorem p_c (l : Fin r) : D.pP l * D.cP l = D.cP l * D.pP l + D.cP l := by
  rw [partialDeriv_def, DAlg.cP, der_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl, one_mul, one_mul]
/- English proof (translation)
Rewrite using `[partialDeriv_def, DAlg.ciP, der_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, one_mul, one_mul, sub_eq_add_neg, multiplierPair_neg]`.
-/
theorem p_ci (l : Fin r) : D.pP l * D.ciP l = D.ciP l * D.pP l - D.ciP l := by
  rw [partialDeriv_def, DAlg.ciP, der_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, one_mul, one_mul, sub_eq_add_neg, multiplierPair_neg]

/- English proof (translation)
Introduce `l` and use `⟨by rw [ec hL, if_neg (vc_vz l)], by rw [ec hL, if_neg (vcb_vz l)]⟩`.
-/
theorem zeta_free_of_variable : ZF D (D.x M.vz) := fun l => ⟨by rw [ec hL, if_neg (vc_vz l)], by rw [ec hL, if_neg (vcb_vz l)]⟩
/- English proof (translation)
Introduce `l` and use `⟨by rw [ec hL, if_neg (vc_vzb l)], by rw [ec hL, if_neg (vcb_vzb l)]⟩`.
-/
theorem zf_zb : ZF D (D.x M.vzb) := fun l => ⟨by rw [ec hL, if_neg (vc_vzb l)], by rw [ec hL, if_neg (vcb_vzb l)]⟩
/- English proof (translation)
Introduce `l` and use `⟨by rw [eci hL, if_neg (vc_vz l)], by rw [eci hL, if_neg (vcb_vz l)]⟩`.
-/
theorem zf_zi : ZF D (D.inv (D.x M.vz)) := fun l => ⟨by rw [eci hL, if_neg (vc_vz l)], by rw [eci hL, if_neg (vcb_vz l)]⟩
/- English proof (translation)
Introduce `l` and use `⟨by rw [eci hL, if_neg (vc_vzb l)], by rw [eci hL, if_neg (vcb_vzb l)]⟩`.
-/
theorem zf_zbi : ZF D (D.inv (D.x M.vzb)) :=
  fun l => ⟨by rw [eci hL, if_neg (vc_vzb l)], by rw [eci hL, if_neg (vcb_vzb l)]⟩
/- English proof (translation)
Introduce `l` and use `⟨euler_gamma_vanish hL _ (vc_vz l) (vc_vzb l), euler_gamma_vanish hL _ (vcb_vz l) (vcb_vzb l)⟩`.
-/
theorem zf_gg : ZF D (D.gg TT) := fun l =>
  ⟨euler_gamma_vanish hL _ (vc_vz l) (vc_vzb l), euler_gamma_vanish hL _ (vcb_vz l) (vcb_vzb l)⟩
/- English proof (translation)
Introduce `l` and use `⟨euler_gamma_inv_vanish hL _ (vc_vz l) (vc_vzb l), euler_gamma_inv_vanish hL _ (vcb_vz l) (vcb_vzb l)⟩`.
-/
theorem zf_ggi : ZF D (D.inv (D.gg TT)) := fun l =>
  ⟨euler_gamma_inv_vanish hL _ (vc_vz l) (vc_vzb l), euler_gamma_inv_vanish hL _ (vcb_vz l) (vcb_vzb l)⟩
omit hL in
/- English proof (translation)
Introduce `l` and use `⟨by rw [hL.leibniz, (hf l).1, (hg l).1]; simp, by rw [hL.leibniz, (hf l).2, (hg l).2]; simp⟩`.
-/
theorem zf_mul' (hL : D.Laws TT) {f g : D.R} (hf : ZF D f) (hg : ZF D g) : ZF D (f * g) := fun l =>
  ⟨by rw [hL.leibniz, (hf l).1, (hg l).1]; simp, by rw [hL.leibniz, (hf l).2, (hg l).2]; simp⟩
omit hL in
/- English proof (translation)
Introduce `l` and use `⟨by rw [map_smul, (hf l).1, smul_zero], by rw [map_smul, (hf l).2, smul_zero]⟩`.
-/
theorem zf_smul {f : D.R} (z : ℂ) (hf : ZF D f) : ZF D (z • f) := fun l =>
  ⟨by rw [map_smul, (hf l).1, smul_zero], by rw [map_smul, (hf l).2, smul_zero]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [ec hL, if_neg (vc_vz m).symm], by rw [ec hL, if_neg (vc_vzb m).symm]⟩`.
-/
theorem cf_c (m : Fin r) : CF D (D.x (M.vc m)) := ⟨by rw [ec hL, if_neg (vc_vz m).symm], by rw [ec hL, if_neg (vc_vzb m).symm]⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [ec hL, if_neg (vcb_vz m).symm], by rw [ec hL, if_neg (vcb_vzb m).symm]⟩`.
-/
theorem cf_cb (m : Fin r) : CF D (D.x (M.vcb m)) :=
  ⟨by rw [ec hL, if_neg (vcb_vz m).symm], by rw [ec hL, if_neg (vcb_vzb m).symm]⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [eci hL, if_neg (vc_vz m).symm], by rw [eci hL, if_neg (vc_vzb m).symm]⟩`.
-/
theorem cf_ci (m : Fin r) : CF D (D.inv (D.x (M.vc m))) :=
  ⟨by rw [eci hL, if_neg (vc_vz m).symm], by rw [eci hL, if_neg (vc_vzb m).symm]⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [eci hL, if_neg (vcb_vz m).symm], by rw [eci hL, if_neg (vcb_vzb m).symm]⟩`.
-/
theorem cf_cbi (m : Fin r) : CF D (D.inv (D.x (M.vcb m))) :=
  ⟨by rw [eci hL, if_neg (vcb_vz m).symm], by rw [eci hL, if_neg (vcb_vzb m).symm]⟩

/- English proof (translation)
Rewrite using `[partialDeriv_def, der_fn hL, one_mul, one_mul]`.
-/
theorem partialDeriv_mul_fn (l : Fin r) (f fb : D.R) :
    D.pP l * D.fnP f fb = D.fnP f fb * D.pP l + D.fnP (D.ev (M.vc l) f) (D.ev (M.vcb l) fb) := by
  rw [partialDeriv_def, der_fn hL, one_mul, one_mul]
/- English proof (translation)
Rewrite using `[partialDerivBar_def, der_fn hL, one_mul, one_mul]`.
-/
theorem partialDerivBar_mul_fn (l : Fin r) (f fb : D.R) :
    D.pbP l * D.fnP f fb = D.fnP f fb * D.pbP l + D.fnP (D.ev (M.vcb l) f) (D.ev (M.vc l) fb) := by
  rw [partialDerivBar_def, der_fn hL, one_mul, one_mul]

/- English proof (translation)
Unfold `nabE`. Rewrite using `[DAlg.zbP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn hL, ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).1, ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).2, multiplierPair_zero, add_zero]`. Use `congr 1`. Apply `mk_comm` to reduce the goal to its premises. Conclude with `comm_eu hL _ _ _ (zf_zi hL l).1`.

Rewrite using `[neg_mul_neg, neg_mul_neg]`. Conclude with `comm_eu hL _ _ _ (zf_zbi hL l).2`.
-/
theorem partialDeriv_commute_nab (l : Fin r) (a : ℝ) : D.pP l * nabE D a TT = nabE D a TT * D.pP l := by
  unfold nabE
  rw [DAlg.zbP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn hL,
    ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).1, ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).2, multiplierPair_zero,
    add_zero]
  congr 1
  apply mk_comm
  · exact comm_eu hL _ _ _ (zf_zi hL l).1
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu hL _ _ _ (zf_zbi hL l).2
/- English proof (translation)
Unfold `nabE`. Rewrite using `[DAlg.zbP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDerivBar_mul_fn hL, ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).2, ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).1, multiplierPair_zero, add_zero]`. Use `congr 1`. Apply `mk_comm` to reduce the goal to its premises. Conclude with `comm_eu hL _ _ _ (zf_zi hL l).2`.

Rewrite using `[neg_mul_neg, neg_mul_neg]`. Conclude with `comm_eu hL _ _ _ (zf_zbi hL l).1`.
-/
theorem partialDerivBar_commute_nab (l : Fin r) (a : ℝ) : D.pbP l * nabE D a TT = nabE D a TT * D.pbP l := by
  unfold nabE
  rw [DAlg.zbP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDerivBar_mul_fn hL,
    ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).2, ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).1, multiplierPair_zero,
    add_zero]
  congr 1
  apply mk_comm
  · exact comm_eu hL _ _ _ (zf_zi hL l).2
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu hL _ _ _ (zf_zbi hL l).1
/- English proof (translation)
Unfold `nabsE`. Rewrite using `[DAlg.zP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn hL, ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).1, ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).2, multiplierPair_zero, add_zero, mul_neg, neg_mul]`. Use `congr 2`. Apply `mk_comm` to reduce the goal to its premises. Conclude with `comm_eu hL _ _ _ (zf_zbi hL l).1`.

Rewrite using `[neg_mul_neg, neg_mul_neg]`. Conclude with `comm_eu hL _ _ _ (zf_zi hL l).2`.
-/
theorem partialDeriv_commute_nabs (l : Fin r) (a : ℝ) : D.pP l * nabsE D a TT = nabsE D a TT * D.pP l := by
  unfold nabsE
  rw [DAlg.zP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDeriv_mul_fn hL,
    ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).1, ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).2, multiplierPair_zero,
    add_zero, mul_neg, neg_mul]
  congr 2
  apply mk_comm
  · exact comm_eu hL _ _ _ (zf_zbi hL l).1
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu hL _ _ _ (zf_zi hL l).2
/- English proof (translation)
Unfold `nabsE`. Rewrite using `[DAlg.zP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDerivBar_mul_fn hL, ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).2, ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).1, multiplierPair_zero, add_zero, mul_neg, neg_mul]`. Use `congr 2`. Apply `mk_comm` to reduce the goal to its premises. Conclude with `comm_eu hL _ _ _ (zf_zbi hL l).2`.

Rewrite using `[neg_mul_neg, neg_mul_neg]`. Conclude with `comm_eu hL _ _ _ (zf_zi hL l).1`.
-/
theorem partialDerivBar_commute_nabs (l : Fin r) (a : ℝ) : D.pbP l * nabsE D a TT = nabsE D a TT * D.pbP l := by
  unfold nabsE
  rw [DAlg.zP, DAlg.ggiP, multiplierPair_mul, smul_fnP, mul_add, add_mul, partialDerivBar_mul_fn hL,
    ((zf_smul _ (zf_mul' hL (zeta_free_of_variable hL) (zf_ggi hL))) l).2, ((zf_smul _ (zf_mul' hL (zf_zb hL) (zf_ggi hL))) l).1, multiplierPair_zero,
    add_zero, mul_neg, neg_mul]
  congr 2
  apply mk_comm
  · exact comm_eu hL _ _ _ (zf_zbi hL l).2
  · rw [neg_mul_neg, neg_mul_neg]; exact comm_eu hL _ _ _ (zf_zi hL l).1

/- English proof (translation)
Rewrite using `[partialDeriv_mul_fn hL, h1, h2, multiplierPair_zero, add_zero]`.
-/
theorem pP_0 (l : Fin r) (f fb : D.R) (h1 : D.ev (M.vc l) f = 0) (h2 : D.ev (M.vcb l) fb = 0) :
    D.pP l * D.fnP f fb = D.fnP f fb * D.pP l := by rw [partialDeriv_mul_fn hL, h1, h2, multiplierPair_zero, add_zero]
/- English proof (translation)
Rewrite using `[partialDerivBar_mul_fn hL, h1, h2, multiplierPair_zero, add_zero]`.
-/
theorem pbP_0 (l : Fin r) (f fb : D.R) (h1 : D.ev (M.vcb l) f = 0) (h2 : D.ev (M.vc l) fb = 0) :
    D.pbP l * D.fnP f fb = D.fnP f fb * D.pbP l := by rw [partialDerivBar_mul_fn hL, h1, h2, multiplierPair_zero, add_zero]

/- English proof (translation)
Establish `h1 : D.ev M.vzb (D.inv (D.x M.vz)) = 0` using `by rw [eci hL, if_neg vz_ne.symm]`. Establish `h2 : D.ev M.vz (D.inv (D.x M.vzb)) = 0` using `by rw [eci hL, if_neg vz_ne]`. Establish `a1` using `comm_eu hL M.vzb M.vz _ h1`. Establish `a2` using `comm_eu hL M.vz M.vzb _ h2`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = (D.mulOp (D.inv (D.x M.vz)) * D.mulOp (D.inv (D.x M.vzb))) * (D.ev M.vzb * D.ev M.vz) := by`. Rewrite using `[mulOp_mul, mulOp_mul, mul_comm (D.inv (D.x M.vzb)) (D.inv (D.x M.vz)), hL.comm M.vz M.vzb]`. Use `_ = D.mulOp (D.inv (D.x M.vz)) * ((D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) * D.ev M.vz) := by`. Simplify using `only [mul_assoc]`.

Use `_ = D.mulOp (D.inv (D.x M.vz)) * (D.ev M.vz * (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb)) := by rw [a2]`. Use `_ = (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) * (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) := (mul_assoc _ _ _).symm`.
-/
theorem dd_comm : (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) * (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) =
    (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) * (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) := by
  have h1 : D.ev M.vzb (D.inv (D.x M.vz)) = 0 := by rw [eci hL, if_neg vz_ne.symm]
  have h2 : D.ev M.vz (D.inv (D.x M.vzb)) = 0 := by rw [eci hL, if_neg vz_ne]
  have a1 := comm_eu hL M.vzb M.vz _ h1
  have a2 := comm_eu hL M.vz M.vzb _ h2
  calc (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) * (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz)
      = D.mulOp (D.inv (D.x M.vzb)) * (D.ev M.vzb * (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz)) := mul_assoc _ _ _
    _ = D.mulOp (D.inv (D.x M.vzb)) * ((D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) * D.ev M.vzb) := by rw [a1]
    _ = (D.mulOp (D.inv (D.x M.vzb)) * D.mulOp (D.inv (D.x M.vz))) * (D.ev M.vz * D.ev M.vzb) := by
        simp only [mul_assoc]
    _ = (D.mulOp (D.inv (D.x M.vz)) * D.mulOp (D.inv (D.x M.vzb))) * (D.ev M.vzb * D.ev M.vz) := by
        rw [mulOp_mul, mulOp_mul, mul_comm (D.inv (D.x M.vzb)) (D.inv (D.x M.vz)), hL.comm M.vz M.vzb]
    _ = D.mulOp (D.inv (D.x M.vz)) * ((D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) * D.ev M.vz) := by
        simp only [mul_assoc]
    _ = D.mulOp (D.inv (D.x M.vz)) * (D.ev M.vz * (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb)) := by rw [a2]
    _ = (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) * (D.mulOp (D.inv (D.x M.vzb)) * D.ev M.vzb) :=
        (mul_assoc _ _ _).symm

/- English proof (translation)
Apply `mk_comm` to reduce the goal to its premises. Conclude with `dd_comm hL`. Rewrite using `[neg_mul_neg, neg_mul_neg]`. Conclude with `(dd_comm hL).symm`.
-/
theorem dz_comm : D.dzbP * D.dzP = D.dzP * D.dzbP := by
  apply mk_comm
  · exact dd_comm hL
  · rw [neg_mul_neg, neg_mul_neg]; exact (dd_comm hL).symm

/- English proof (translation)
Establish `hg : D.x M.vz * D.x M.vzb = D.gg TT + algebraMap ℂ D.R (TT : ℂ)` using `by unfold DAlg.gg; ring`. Rewrite using `[hL.leibniz, ec hL, if_pos rfl, ev_inv hL _ _ hL.unit_gg, euler_gg_zb hL, hg]`. Take the linear combination `(D.inv (D.gg TT) - D.inv (D.gg TT) * D.inv (D.gg TT) * (D.gg TT + algebraMap ℂ D.R (TT : ℂ))) * hzb hL + (-(D.inv (D.gg TT))) * hgi hL`.
-/
theorem key_zb : D.inv (D.x M.vzb) * D.ev M.vzb (D.x M.vzb * D.inv (D.gg TT)) =
    -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT))) := by
  have hg : D.x M.vz * D.x M.vzb = D.gg TT + algebraMap ℂ D.R (TT : ℂ) := by unfold DAlg.gg; ring
  rw [hL.leibniz, ec hL, if_pos rfl, ev_inv hL _ _ hL.unit_gg, euler_gg_zb hL, hg]
  linear_combination (D.inv (D.gg TT) - D.inv (D.gg TT) * D.inv (D.gg TT) * (D.gg TT + algebraMap ℂ D.R (TT : ℂ)))
    * hzb hL + (-(D.inv (D.gg TT))) * hgi hL

/- English proof (translation)
Establish `hg : D.x M.vz * D.x M.vzb = D.gg TT + algebraMap ℂ D.R (TT : ℂ)` using `by unfold DAlg.gg; ring`. Rewrite using `[hL.leibniz, ec hL, if_pos rfl, ev_inv hL _ _ hL.unit_gg, euler_GG_z hL, hg]`. Take the linear combination `(D.inv (D.gg TT) - D.inv (D.gg TT) * D.inv (D.gg TT) * (D.gg TT + algebraMap ℂ D.R (TT : ℂ))) * hz hL + (-(D.inv (D.gg TT))) * hgi hL`.
-/
theorem euler_zeta_gamma_inv_identity : D.inv (D.x M.vz) * D.ev M.vz (D.x M.vz * D.inv (D.gg TT)) =
    -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT))) := by
  have hg : D.x M.vz * D.x M.vzb = D.gg TT + algebraMap ℂ D.R (TT : ℂ) := by unfold DAlg.gg; ring
  rw [hL.leibniz, ec hL, if_pos rfl, ev_inv hL _ _ hL.unit_gg, euler_GG_z hL, hg]
  linear_combination (D.inv (D.gg TT) - D.inv (D.gg TT) * D.inv (D.gg TT) * (D.gg TT + algebraMap ℂ D.R (TT : ℂ)))
    * hz hL + (-(D.inv (D.gg TT))) * hgi hL

/- English proof (translation)
Establish `e1 : D.dzbP * D.fnP ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) = D.fnP ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) * D.dzbP + D.fnP (D.inv (D.x M.vzb) * D.ev M.vzb ((a : ℂ) • (D.x M.vzb * D.inv (D.gg T …`. Rewrite using `[DAlg.dzbP, der_fn hL]`. Establish `e2 : D.dzP * D.fnP ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) = D.fnP ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) * D.dzP + D.fnP (D.inv (D.x M.vz) * D.ev M.vz ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT)))) …`. Rewrite using `[DAlg.dzP, der_fn hL]`. Rewrite using `[mul_assoc, ← Algebra.smul_def, DAlg.zP, DAlg.zbP, DAlg.ggiP, multiplierPair_mul, multiplierPair_mul, multiplierPair_mul, smul_fnP, smul_fnP, smul_fnP]`.

Simplify using `only [map_smul, mul_smul_comm, euler_zeta_gamma_inv_identity hL, key_zb hL] at e1 e2`. Establish `e3` using `multiplierPair_comm D ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT)))`. Establish `e4 : D.fnP (((2 * a * TT : ℝ) : ℂ) • (D.inv (D.gg TT) * D.inv (D.gg TT))) (((2 * a * TT : ℝ) : ℂ) • (D.inv (D.gg TT) * D.inv (D.gg TT))) = -D.fnP ((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT)))) ((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg T …`. Rewrite using `[multiplierPair_neg, sub_eq_add_neg, multiplierPair_neg, multiplierPair_add]`. Establish `: (((2 * a * TT : ℝ) : ℂ) • (D.inv (D.gg TT) * D.inv (D.gg TT))) = -((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT)))) + -((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT))))`.

Simplify using `only [Algebra.smul_def]`. Use `push_cast`. Simplify using `only [map_ofNat, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← this]`.

Rewrite using `[e4]`. Simplify using `only [add_mul, mul_add, neg_mul, mul_neg]`. Rewrite using `[e1, e2, e3, dz_comm hL]`. Normalize the expressions using the abelian group laws.
-/
theorem curv (a : ℝ) :
    (-D.dzbP + (a : ℂ) • (D.zP * D.ggiP TT)) * (D.dzP + (a : ℂ) • (D.zbP * D.ggiP TT)) -
      (D.dzP + (a : ℂ) • (D.zbP * D.ggiP TT)) * (-D.dzbP + (a : ℂ) • (D.zP * D.ggiP TT)) =
      (algebraMap ℂ D.Pr ((2 * a * TT : ℝ) : ℂ)) * D.ggiP TT * D.ggiP TT := by
  have e1 : D.dzbP * D.fnP ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) =
      D.fnP ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) * D.dzbP +
      D.fnP (D.inv (D.x M.vzb) * D.ev M.vzb ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))))
        (D.inv (D.x M.vz) * D.ev M.vz ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT)))) := by
    rw [DAlg.dzbP, der_fn hL]
  have e2 : D.dzP * D.fnP ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) =
      D.fnP ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) * D.dzP +
      D.fnP (D.inv (D.x M.vz) * D.ev M.vz ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))))
        (D.inv (D.x M.vzb) * D.ev M.vzb ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT)))) := by
    rw [DAlg.dzP, der_fn hL]
  rw [mul_assoc, ← Algebra.smul_def, DAlg.zP, DAlg.zbP, DAlg.ggiP, multiplierPair_mul, multiplierPair_mul, multiplierPair_mul, smul_fnP, smul_fnP,
    smul_fnP]
  simp only [map_smul, mul_smul_comm, euler_zeta_gamma_inv_identity hL, key_zb hL] at e1 e2
  have e3 := multiplierPair_comm D ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT)))
    ((a : ℂ) • (D.x M.vzb * D.inv (D.gg TT))) ((a : ℂ) • (D.x M.vz * D.inv (D.gg TT)))
  have e4 : D.fnP (((2 * a * TT : ℝ) : ℂ) • (D.inv (D.gg TT) * D.inv (D.gg TT)))
      (((2 * a * TT : ℝ) : ℂ) • (D.inv (D.gg TT) * D.inv (D.gg TT))) =
      -D.fnP ((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT))))
        ((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT)))) -
      D.fnP ((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT))))
        ((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT)))) := by
    rw [multiplierPair_neg, sub_eq_add_neg, multiplierPair_neg, multiplierPair_add]
    have : (((2 * a * TT : ℝ) : ℂ) • (D.inv (D.gg TT) * D.inv (D.gg TT))) =
        -((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT)))) +
        -((a : ℂ) • -(algebraMap ℂ D.R (TT : ℂ) * (D.inv (D.gg TT) * D.inv (D.gg TT)))) := by
      simp only [Algebra.smul_def]
      push_cast
      simp only [map_ofNat, map_mul]
      ring
    rw [← this]
  rw [e4]
  simp only [add_mul, mul_add, neg_mul, mul_neg]
  rw [e1, e2, e3, dz_comm hL]
  abel

end Line

section Mat

variable (P : Par) (D : DAlg P.r) [hF : Fact (D.Laws P.TT)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nabA_eq : nabA P D = Matrix.diagonal fun π => nabE D (aC P π) P.TT := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nabsA_eq : nabsA P D = Matrix.diagonal fun π => nabsE D (aC P π) P.TT := rfl

local macro "mx2_dg" : tactic => `(tactic| (simp only [pA, pbA, cA, ciA, cbA, cbiA, zA, ziA, zbA, zbiA, ggA, ggiA, nabA_eq, nabsA_eq, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add, Matrix.diagonal_sub, ← Matrix.diagonal_one]; congr 1; funext π))

/- English proof (translation)
Introduce `P D _`. Establish `hL : D.Laws P.TT` using `Fact.out`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `mx2_dg`. Conclude with `nabla_zeta_comm hL _`.

Use `mx2_dg`. Conclude with `nab_zi hL _`. Use `mx2_dg`. Conclude with `nab_zb hL _`. Use the proof step `mx2_dg; exact nab_cf hL _ _ _ (by rw [eci hL, if_neg vz_ne]) (by rw [eci hL, if_neg vz_ne.symm])`.

Use `mx2_dg`. Conclude with `nab_gg hL _`. Use `mx2_dg`. Conclude with `nab_ggi hL _`. Introduce and unpack `x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)`.

Use `mx2_dg`. Conclude with `nab_cf hL _ _ _ (cf_c hL m).1 (cf_cb hL m).2`. Use `mx2_dg`. Conclude with `nab_cf hL _ _ _ (cf_ci hL m).1 (cf_cbi hL m).2`. Use `mx2_dg`.

Conclude with `nab_cf hL _ _ _ (cf_cb hL m).1 (cf_c hL m).2`. Use `mx2_dg`. Conclude with `nab_cf hL _ _ _ (cf_cbi hL m).1 (cf_ci hL m).2`.
-/
theorem levNab : LevNab := by
  intro P D _
  have hL : D.Laws P.TT := Fact.out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mx2_dg; exact nabla_zeta_comm hL _
  · mx2_dg; exact nab_zi hL _
  · mx2_dg; exact nab_zb hL _
  · mx2_dg; exact nab_cf hL _ _ _ (by rw [eci hL, if_neg vz_ne]) (by rw [eci hL, if_neg vz_ne.symm])
  · mx2_dg; exact nab_gg hL _
  · mx2_dg; exact nab_ggi hL _
  · rintro x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    · mx2_dg; exact nab_cf hL _ _ _ (cf_c hL m).1 (cf_cb hL m).2
    · mx2_dg; exact nab_cf hL _ _ _ (cf_ci hL m).1 (cf_cbi hL m).2
    · mx2_dg; exact nab_cf hL _ _ _ (cf_cb hL m).1 (cf_c hL m).2
    · mx2_dg; exact nab_cf hL _ _ _ (cf_cbi hL m).1 (cf_ci hL m).2

/- English proof (translation)
Introduce `P D _`. Establish `hL : D.Laws P.TT` using `Fact.out`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `mx2_dg`. Conclude with `nabs_zb hL _`.

Use `mx2_dg`. Conclude with `nabs_zbi hL _`. Use the proof step `mx2_dg; exact nabs_cf hL _ _ _ (by rw [ec hL, if_neg vz_ne.symm]) (by rw [ec hL, if_neg vz_ne])`. Use the proof step `mx2_dg; exact nabs_cf hL _ _ _ (by rw [eci hL, if_neg vz_ne.symm]) (by rw [eci hL, if_neg vz_ne])`. Use `mx2_dg`.

Conclude with `nabs_gg hL _`. Use `mx2_dg`. Conclude with `nabs_ggi hL _`. Introduce and unpack `x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)`. Use `mx2_dg`.

Conclude with `nabs_cf hL _ _ _ (cf_c hL m).2 (cf_cb hL m).1`. Use `mx2_dg`. Conclude with `nabs_cf hL _ _ _ (cf_ci hL m).2 (cf_cbi hL m).1`. Use `mx2_dg`. Conclude with `nabs_cf hL _ _ _ (cf_cb hL m).2 (cf_c hL m).1`.

Use `mx2_dg`. Conclude with `nabs_cf hL _ _ _ (cf_cbi hL m).2 (cf_ci hL m).1`.
-/
theorem levNabs : LevNabs := by
  intro P D _
  have hL : D.Laws P.TT := Fact.out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mx2_dg; exact nabs_zb hL _
  · mx2_dg; exact nabs_zbi hL _
  · mx2_dg; exact nabs_cf hL _ _ _ (by rw [ec hL, if_neg vz_ne.symm]) (by rw [ec hL, if_neg vz_ne])
  · mx2_dg; exact nabs_cf hL _ _ _ (by rw [eci hL, if_neg vz_ne.symm]) (by rw [eci hL, if_neg vz_ne])
  · mx2_dg; exact nabs_gg hL _
  · mx2_dg; exact nabs_ggi hL _
  · rintro x (((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩)
    · mx2_dg; exact nabs_cf hL _ _ _ (cf_c hL m).2 (cf_cb hL m).1
    · mx2_dg; exact nabs_cf hL _ _ _ (cf_ci hL m).2 (cf_cbi hL m).1
    · mx2_dg; exact nabs_cf hL _ _ _ (cf_cb hL m).2 (cf_c hL m).1
    · mx2_dg; exact nabs_cf hL _ _ _ (cf_cbi hL m).2 (cf_ci hL m).1

/- English proof (translation)
Introduce `P D _ l m`. Establish `hL : D.Laws P.TT` using `Fact.out`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use the proof step `mx2_dg; exact mk_comm D _ _ _ _ (hL.comm _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact hL.comm _ _)`. Use the proof step `mx2_dg; exact mk_comm D _ _ _ _ (hL.comm _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact hL.comm _ _)`.

Use the proof step `mx2_dg; exact mk_comm D _ _ _ _ (hL.comm _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact hL.comm _ _)`. Use `mx2_dg`. Conclude with `partialDeriv_commute_nab hL _ _`. Use `mx2_dg`. Conclude with `partialDerivBar_commute_nab hL _ _`.

Use `mx2_dg`. Conclude with `partialDeriv_commute_nabs hL _ _`. Use `mx2_dg`. Conclude with `partialDerivBar_commute_nabs hL _ _`.
-/
theorem levPP : LevPP := by
  intro P D _ l m
  have hL : D.Laws P.TT := Fact.out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · mx2_dg; exact mk_comm D _ _ _ _ (hL.comm _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact hL.comm _ _)
  · mx2_dg; exact mk_comm D _ _ _ _ (hL.comm _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact hL.comm _ _)
  · mx2_dg; exact mk_comm D _ _ _ _ (hL.comm _ _) (by rw [neg_mul_neg, neg_mul_neg]; exact hL.comm _ _)
  · mx2_dg; exact partialDeriv_commute_nab hL _ _
  · mx2_dg; exact partialDerivBar_commute_nab hL _ _
  · mx2_dg; exact partialDeriv_commute_nabs hL _ _
  · mx2_dg; exact partialDerivBar_commute_nabs hL _ _

/- English proof (translation)
Introduce `P D _ l`. Establish `hL : D.Laws P.TT` using `Fact.out`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`. Distinguish the cases in `h : l = m`.

Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`. Use `mx2_dg`. Conclude with `p_c hL l`. Rewrite using `[if_neg h, add_zero]`.

Use `mx2_dg`. Conclude with `pP_0 hL _ _ _ (by rw [ec hL, if_neg (fun e => h ((vc_inj _ _).1 e))]) (by rw [ec hL, if_neg (fun e => h ((vcb_inj _ _).1 e))])`. Introduce `m`. Distinguish the cases in `h : l = m`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl]`. Use `mx2_dg`. Conclude with `p_ci hL l`. Rewrite using `[if_neg h, sub_zero]`. Use `mx2_dg`.

Conclude with `pP_0 hL _ _ _ (by rw [eci hL, if_neg (fun e => h ((vc_inj _ _).1 e))]) (by rw [eci hL, if_neg (fun e => h ((vcb_inj _ _).1 e))])`. Introduce and unpack `x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)`. Use the proof step `mx2_dg; exact pP_0 hL _ _ _ (by rw [ec hL, if_neg (vc_vcb _ _)]) (by rw [ec hL, if_neg (vc_vcb _ _).symm])`. Use the proof step `mx2_dg; exact pP_0 hL _ _ _ (by rw [eci hL, if_neg (vc_vcb _ _)]) (by rw [eci hL, if_neg (vc_vcb _ _).symm])`. Simplify using `only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`.

Break down `hx with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Use `mx2_dg`. Conclude with `pP_0 hL _ _ _ (zeta_free_of_variable hL l).1 (zf_zb hL l).2`. Use `mx2_dg`. Conclude with `pP_0 hL _ _ _ (zf_zi hL l).1 (zf_zbi hL l).2`.

Use `mx2_dg`. Conclude with `pP_0 hL _ _ _ (zf_zb hL l).1 (zeta_free_of_variable hL l).2`. Use `mx2_dg`. Conclude with `pP_0 hL _ _ _ (zf_zbi hL l).1 (zf_zi hL l).2`. Use `mx2_dg`.

Conclude with `pP_0 hL _ _ _ (zf_gg hL l).1 (zf_gg hL l).2`. Use `mx2_dg`. Conclude with `pP_0 hL _ _ _ (zf_ggi hL l).1 (zf_ggi hL l).2`.
-/
theorem levP : LevP := by
  intro P D _ l
  have hL : D.Laws P.TT := Fact.out
  refine ⟨?_, ?_, ?_⟩
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg; exact p_c hL l
    · rw [if_neg h, add_zero]; mx2_dg
      exact pP_0 hL _ _ _ (by rw [ec hL, if_neg (fun e => h ((vc_inj _ _).1 e))])
        (by rw [ec hL, if_neg (fun e => h ((vcb_inj _ _).1 e))])
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg; exact p_ci hL l
    · rw [if_neg h, sub_zero]; mx2_dg
      exact pP_0 hL _ _ _ (by rw [eci hL, if_neg (fun e => h ((vc_inj _ _).1 e))])
        (by rw [eci hL, if_neg (fun e => h ((vcb_inj _ _).1 e))])
  · rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)
    · mx2_dg; exact pP_0 hL _ _ _ (by rw [ec hL, if_neg (vc_vcb _ _)]) (by rw [ec hL, if_neg (vc_vcb _ _).symm])
    · mx2_dg; exact pP_0 hL _ _ _ (by rw [eci hL, if_neg (vc_vcb _ _)]) (by rw [eci hL, if_neg (vc_vcb _ _).symm])
    · simp only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · mx2_dg; exact pP_0 hL _ _ _ (zeta_free_of_variable hL l).1 (zf_zb hL l).2
      · mx2_dg; exact pP_0 hL _ _ _ (zf_zi hL l).1 (zf_zbi hL l).2
      · mx2_dg; exact pP_0 hL _ _ _ (zf_zb hL l).1 (zeta_free_of_variable hL l).2
      · mx2_dg; exact pP_0 hL _ _ _ (zf_zbi hL l).1 (zf_zi hL l).2
      · mx2_dg; exact pP_0 hL _ _ _ (zf_gg hL l).1 (zf_gg hL l).2
      · mx2_dg; exact pP_0 hL _ _ _ (zf_ggi hL l).1 (zf_ggi hL l).2

/- English proof (translation)
Introduce `P D _ l`. Establish `hL : D.Laws P.TT` using `Fact.out`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m`. Distinguish the cases in `h : l = m`.

Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`. Use `mx2_dg`. Rewrite using `[DAlg.cbP, partialDerivBar_mul_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl]`. Rewrite using `[if_neg h, add_zero]`.

Use `mx2_dg`. Conclude with `pbP_0 hL _ _ _ (by rw [ec hL, if_neg (fun e => h ((vcb_inj _ _).1 e))]) (by rw [ec hL, if_neg (fun e => h ((vc_inj _ _).1 e))])`. Introduce `m`. Distinguish the cases in `h : l = m`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl]`. Use `mx2_dg`. Rewrite using `[DAlg.cbiP, partialDerivBar_mul_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, sub_eq_add_neg, multiplierPair_neg]`. Rewrite using `[if_neg h, sub_zero]`. Use `mx2_dg`.

Conclude with `pbP_0 hL _ _ _ (by rw [eci hL, if_neg (fun e => h ((vcb_inj _ _).1 e))]) (by rw [eci hL, if_neg (fun e => h ((vc_inj _ _).1 e))])`. Introduce and unpack `x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)`. Use the proof step `mx2_dg; exact pbP_0 hL _ _ _ (by rw [ec hL, if_neg (vc_vcb _ _).symm]) (by rw [ec hL, if_neg (vc_vcb _ _)])`. Use the proof step `mx2_dg; exact pbP_0 hL _ _ _ (by rw [eci hL, if_neg (vc_vcb _ _).symm]) (by rw [eci hL, if_neg (vc_vcb _ _)])`. Simplify using `only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`.

Break down `hx with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Use `mx2_dg`. Conclude with `pbP_0 hL _ _ _ (zeta_free_of_variable hL l).2 (zf_zb hL l).1`. Use `mx2_dg`. Conclude with `pbP_0 hL _ _ _ (zf_zi hL l).2 (zf_zbi hL l).1`.

Use `mx2_dg`. Conclude with `pbP_0 hL _ _ _ (zf_zb hL l).2 (zeta_free_of_variable hL l).1`. Use `mx2_dg`. Conclude with `pbP_0 hL _ _ _ (zf_zbi hL l).2 (zf_zi hL l).1`. Use `mx2_dg`.

Conclude with `pbP_0 hL _ _ _ (zf_gg hL l).2 (zf_gg hL l).1`. Use `mx2_dg`. Conclude with `pbP_0 hL _ _ _ (zf_ggi hL l).2 (zf_ggi hL l).1`.
-/
theorem levPb : LevPb := by
  intro P D _ l
  have hL : D.Laws P.TT := Fact.out
  refine ⟨?_, ?_, ?_⟩
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg
      rw [DAlg.cbP, partialDerivBar_mul_fn hL, ec hL, ec hL, if_pos rfl, if_pos rfl]
    · rw [if_neg h, add_zero]; mx2_dg
      exact pbP_0 hL _ _ _ (by rw [ec hL, if_neg (fun e => h ((vcb_inj _ _).1 e))])
        (by rw [ec hL, if_neg (fun e => h ((vc_inj _ _).1 e))])
  · intro m
    by_cases h : l = m
    · subst h; rw [if_pos rfl]; mx2_dg
      rw [DAlg.cbiP, partialDerivBar_mul_fn hL, eci hL, eci hL, if_pos rfl, if_pos rfl, sub_eq_add_neg, multiplierPair_neg]
    · rw [if_neg h, sub_zero]; mx2_dg
      exact pbP_0 hL _ _ _ (by rw [eci hL, if_neg (fun e => h ((vcb_inj _ _).1 e))])
        (by rw [eci hL, if_neg (fun e => h ((vc_inj _ _).1 e))])
  · rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩) | hx)
    · mx2_dg; exact pbP_0 hL _ _ _ (by rw [ec hL, if_neg (vc_vcb _ _).symm]) (by rw [ec hL, if_neg (vc_vcb _ _)])
    · mx2_dg; exact pbP_0 hL _ _ _ (by rw [eci hL, if_neg (vc_vcb _ _).symm]) (by rw [eci hL, if_neg (vc_vcb _ _)])
    · simp only [zfnsA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · mx2_dg; exact pbP_0 hL _ _ _ (zeta_free_of_variable hL l).2 (zf_zb hL l).1
      · mx2_dg; exact pbP_0 hL _ _ _ (zf_zi hL l).2 (zf_zbi hL l).1
      · mx2_dg; exact pbP_0 hL _ _ _ (zf_zb hL l).2 (zeta_free_of_variable hL l).1
      · mx2_dg; exact pbP_0 hL _ _ _ (zf_zbi hL l).2 (zf_zi hL l).1
      · mx2_dg; exact pbP_0 hL _ _ _ (zf_gg hL l).2 (zf_gg hL l).1
      · mx2_dg; exact pbP_0 hL _ _ _ (zf_ggi hL l).2 (zf_ggi hL l).1

/- English proof (translation)
Break down `hx with ((((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩) | hx)` into its components or cases. Conclude with `⟨_, _, rfl⟩`. Conclude with `⟨_, _, rfl⟩`. Conclude with `⟨_, _, rfl⟩`. Conclude with `⟨_, _, rfl⟩`.

Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩`.
-/
theorem form (x : A P D) (hx : x ∈ fnsA P D) : ∃ f fb, x = sc P D (D.fnP f fb) := by
  rcases hx with ((((⟨m, rfl⟩ | ⟨m, rfl⟩) | ⟨m, rfl⟩) | ⟨m, rfl⟩) | hx)
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩

/- English proof (translation)
Introduce `P D _`. Establish `hL : D.Laws P.TT` using `Fact.out`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy`. Take `⟨f, fb, rfl⟩` from `form P D x hx`.

Take `⟨g, gb, rfl⟩` from `form P D y hy`. Use `mx2_dg`. Conclude with `multiplierPair_comm D _ _ _ _`. Introduce `l`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `mx2_dg`. Conclude with `inv1 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`. Conclude with `inv2 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`.

Conclude with `inv1 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`. Conclude with `inv2 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`. Conclude with `inv1 hL _ _ (ux hL _) (ux hL _)`.

Use `mx2_dg`. Conclude with `inv2 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`. Conclude with `inv1 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`.

Conclude with `inv2 hL _ _ (ux hL _) (ux hL _)`. Use `mx2_dg`. Conclude with `inv1 hL _ _ hL.unit_gg hL.unit_gg`. Use `mx2_dg`. Conclude with `inv2 hL _ _ hL.unit_gg hL.unit_gg`.

Rewrite using `[Matrix.algebraMap_eq_diagonal] mx2_dg`. Rewrite using `[Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, ← multiplierPair_one, smul_fnP, DAlg.zP, DAlg.zbP, multiplierPair_mul, sub_eq_add_neg, multiplierPair_neg, multiplierPair_add, DAlg.ggP]`. Use `congr 1`. Unfold `DAlg.gg`. Rewrite using `[Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]`.

Unfold `DAlg.gg`. Rewrite using `[Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, mul_comm]`.
-/
theorem levFns : LevFns := by
  intro P D _
  have hL : D.Laws P.TT := Fact.out
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    obtain ⟨f, fb, rfl⟩ := form P D x hx
    obtain ⟨g, gb, rfl⟩ := form P D y hy
    mx2_dg; exact multiplierPair_comm D _ _ _ _
  · intro l
    refine ⟨?_, ?_, ?_, ?_⟩
    · mx2_dg; exact inv1 hL _ _ (ux hL _) (ux hL _)
    · mx2_dg; exact inv2 hL _ _ (ux hL _) (ux hL _)
    · mx2_dg; exact inv1 hL _ _ (ux hL _) (ux hL _)
    · mx2_dg; exact inv2 hL _ _ (ux hL _) (ux hL _)
  · mx2_dg; exact inv1 hL _ _ (ux hL _) (ux hL _)
  · mx2_dg; exact inv2 hL _ _ (ux hL _) (ux hL _)
  · mx2_dg; exact inv1 hL _ _ (ux hL _) (ux hL _)
  · mx2_dg; exact inv2 hL _ _ (ux hL _) (ux hL _)
  · mx2_dg; exact inv1 hL _ _ hL.unit_gg hL.unit_gg
  · mx2_dg; exact inv2 hL _ _ hL.unit_gg hL.unit_gg
  · rw [Matrix.algebraMap_eq_diagonal]
    mx2_dg
    rw [Pi.algebraMap_apply, Algebra.algebraMap_eq_smul_one, ← multiplierPair_one, smul_fnP, DAlg.zP, DAlg.zbP, multiplierPair_mul,
      sub_eq_add_neg, multiplierPair_neg, multiplierPair_add, DAlg.ggP]
    congr 1
    · unfold DAlg.gg; rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg]
    · unfold DAlg.gg; rw [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, mul_comm]

/- English proof (translation)
Introduce `hF hP hPb hPP hN hNs P D _`. Establish `z1 : zA P D ∈ zfnsA P D` using `by simp [zfnsA]`. Establish `z2 : ziA P D ∈ zfnsA P D` using `by simp [zfnsA]`. Establish `z3 : zbA P D ∈ zfnsA P D` using `by simp [zfnsA]`. Establish `z4 : zbiA P D ∈ zfnsA P D` using `by simp [zfnsA]`.

Establish `z5 : ggA P D ∈ zfnsA P D` using `by simp [zfnsA]`. Establish `z6 : ggiA P D ∈ zfnsA P D` using `by simp [zfnsA]`. Take `⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩` from `hF P D`. Take `⟨n1, n2, n3, n4, n5, n6, n7⟩` from `hN P D`. Take `⟨s1, s2, s3, s4, s5, s6, s7⟩` from `hNs P D`.

Use `⟨{ p := pA P D, pb := pbA P D, c := cA P D, ci := ciA P D, cb := cbA P D, cbi := cbiA P D, ζ := zA P D, ζi := ziA P D, ζb := zbA P D, ζbi := zbiA P D, GG := ggA P D, GGi := ggiA P D, nab := nabA P D, nabs := nabsA P D, TT := (P.TT : ℂ), fns_comm := f0, c_ci := fun l => (f1 l).1, …` and prove the remaining obligations. Conclude with `⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩`.
-/
theorem levelAssemble : LevelAssemble := by
  intro hF hP hPb hPP hN hNs P D _
  have z1 : zA P D ∈ zfnsA P D := by simp [zfnsA]
  have z2 : ziA P D ∈ zfnsA P D := by simp [zfnsA]
  have z3 : zbA P D ∈ zfnsA P D := by simp [zfnsA]
  have z4 : zbiA P D ∈ zfnsA P D := by simp [zfnsA]
  have z5 : ggA P D ∈ zfnsA P D := by simp [zfnsA]
  have z6 : ggiA P D ∈ zfnsA P D := by simp [zfnsA]
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hF P D
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := hN P D
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := hNs P D
  refine ⟨{
    p := pA P D, pb := pbA P D, c := cA P D, ci := ciA P D, cb := cbA P D, cbi := cbiA P D, ζ := zA P D, ζi := ziA P D,
    ζb := zbA P D, ζbi := zbiA P D, GG := ggA P D, GGi := ggiA P D, nab := nabA P D, nabs := nabsA P D, TT := (P.TT : ℂ),
    fns_comm := f0,
    c_ci := fun l => (f1 l).1, ci_c := fun l => (f1 l).2.1, cb_cbi := fun l => (f1 l).2.2.1, cbi_cb := fun l => (f1 l).2.2.2,
    ζ_ζi := f2, ζi_ζ := f3, ζb_ζbi := f4, ζbi_ζb := f5, GG_GGi := f6, GGi_GG := f7, GG_def := f8,
    p_c := fun l m => (hP P D l).1 m, p_ci := fun l m => (hP P D l).2.1 m,
    p_cb := fun l m => (hP P D l).2.2 _ (Or.inl (Or.inl ⟨m, rfl⟩)),
    p_cbi := fun l m => (hP P D l).2.2 _ (Or.inl (Or.inr ⟨m, rfl⟩)),
    p_ζ := fun l => (hP P D l).2.2 _ (Or.inr z1), p_ζi := fun l => (hP P D l).2.2 _ (Or.inr z2),
    p_ζb := fun l => (hP P D l).2.2 _ (Or.inr z3), p_ζbi := fun l => (hP P D l).2.2 _ (Or.inr z4),
    p_GG := fun l => (hP P D l).2.2 _ (Or.inr z5), p_GGi := fun l => (hP P D l).2.2 _ (Or.inr z6),
    pb_cb := fun l m => (hPb P D l).1 m, pb_cbi := fun l m => (hPb P D l).2.1 m,
    pb_c := fun l m => (hPb P D l).2.2 _ (Or.inl (Or.inl ⟨m, rfl⟩)),
    pb_ci := fun l m => (hPb P D l).2.2 _ (Or.inl (Or.inr ⟨m, rfl⟩)),
    pb_ζ := fun l => (hPb P D l).2.2 _ (Or.inr z1), pb_ζi := fun l => (hPb P D l).2.2 _ (Or.inr z2),
    pb_ζb := fun l => (hPb P D l).2.2 _ (Or.inr z3), pb_ζbi := fun l => (hPb P D l).2.2 _ (Or.inr z4),
    pb_GG := fun l => (hPb P D l).2.2 _ (Or.inr z5), pb_GGi := fun l => (hPb P D l).2.2 _ (Or.inr z6),
    p_p := fun l m => (hPP P D l m).1, p_pb := fun l m => (hPP P D l m).2.1, pb_pb := fun l m => (hPP P D l m).2.2.1,
    p_nab := fun l => (hPP P D l l).2.2.2.1, pb_nab := fun l => (hPP P D l l).2.2.2.2.1,
    p_nabs := fun l => (hPP P D l l).2.2.2.2.2.1, pb_nabs := fun l => (hPP P D l l).2.2.2.2.2.2,
    nab_ζ := n1, nab_ζi := n2, nab_ζb := n3, nab_ζbi := n4, nab_GG := n5, nab_GGi := n6,
    nab_c := fun l => n7 _ (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))), nab_ci := fun l => n7 _ (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))),
    nab_cb := fun l => n7 _ (Or.inl (Or.inr ⟨l, rfl⟩)), nab_cbi := fun l => n7 _ (Or.inr ⟨l, rfl⟩),
    nabs_ζb := s1, nabs_ζbi := s2, nabs_ζ := s3, nabs_ζi := s4, nabs_GG := s5, nabs_GGi := s6,
    nabs_c := fun l => s7 _ (Or.inl (Or.inl (Or.inl ⟨l, rfl⟩))), nabs_ci := fun l => s7 _ (Or.inl (Or.inl (Or.inr ⟨l, rfl⟩))),
    nabs_cb := fun l => s7 _ (Or.inl (Or.inr ⟨l, rfl⟩)), nabs_cbi := fun l => s7 _ (Or.inr ⟨l, rfl⟩) }, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- English proof (translation)
The claim follows from `levelAssemble levFns levP levPb levPP levNab levNabs`.
-/
theorem levelExists : LevelExists := levelAssemble levFns levP levPb levPP levNab levNabs

/- English proof (translation)
Simplify using `only [sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Both sides reduce to the same expression.
-/
theorem star_sc (w : D.Pr) : star (sc P D w) = sc P D (star w) := by
  simp only [sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  rfl

/- English proof (translation)
Introduce `P D _`. Use `⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `star_sc P D _`. Conclude with `star_sc P D _`. Rewrite using `[pA, star_sc, pbA, sc, sc, ← map_neg]`.

Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Both sides reduce to the same expression. Use `show MulOpposite.op (D.ev (M.vc l)) = -MulOpposite.op (-D.ev (M.vc l))`. Simplify using the standard rewrite rules.

Conclude with `star_sc P D _`. Conclude with `star_sc P D _`. Conclude with `star_sc P D _`. Conclude with `star_sc P D _`. Simplify using `only [nabA, nabsA, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`.

Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.star_apply, star_add, star_smul, star_mul]`. Establish `h1 : star D.dzP = -D.dzbP`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Both sides reduce to the same expression. Use `show MulOpposite.op (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) = -MulOpposite.op (-(D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz))`. Rewrite using `[MulOpposite.op_neg, neg_neg]`. Establish `h2 : star (D.ggiP P.TT) * star D.zbP = D.zP * D.ggiP P.TT`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use `show D.mulOp _ * D.mulOp _ = D.mulOp _ * D.mulOp _`. Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp, mul_left_comm]`. Use `show MulOpposite.op (D.mulOp _ * D.mulOp _) = MulOpposite.op (D.mulOp _ * D.mulOp _)`. Use `congr 1`.

Use extensionality with `h : 1`. Simplify using `[DAlg.mulOp, mul_left_comm]`. Rewrite using `[h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem starGens : StarGens := by
  intro P D _
  refine ⟨fun l => ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact star_sc P D _
  · exact star_sc P D _
  · rw [pA, star_sc, pbA, sc, sc, ← map_neg]
    congr 1
    refine Prod.ext ?_ ?_
    · rfl
    · show MulOpposite.op (D.ev (M.vc l)) = -MulOpposite.op (-D.ev (M.vc l))
      simp
  · exact star_sc P D _
  · exact star_sc P D _
  · exact star_sc P D _
  · exact star_sc P D _
  · simp only [nabA, nabsA, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext π
    simp only [Pi.star_apply, star_add, star_smul, star_mul]
    have h1 : star D.dzP = -D.dzbP := by
      refine Prod.ext ?_ ?_
      · rfl
      · show MulOpposite.op (D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz) =
          -MulOpposite.op (-(D.mulOp (D.inv (D.x M.vz)) * D.ev M.vz))
        rw [MulOpposite.op_neg, neg_neg]
    have h2 : star (D.ggiP P.TT) * star D.zbP = D.zP * D.ggiP P.TT := by
      refine Prod.ext ?_ ?_
      · show D.mulOp _ * D.mulOp _ = D.mulOp _ * D.mulOp _
        ext h : 1; simp [DAlg.mulOp, mul_left_comm]
      · show MulOpposite.op (D.mulOp _ * D.mulOp _) = MulOpposite.op (D.mulOp _ * D.mulOp _)
        congr 1
        ext h : 1; simp [DAlg.mulOp, mul_left_comm]
    rw [h1, h2]; simp

/- English proof (translation)
Introduce `P D _ L h`. Take `⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, hzb]`. Conclude with `(starGens P D).2.1`.

Rewrite using `[hn, hns]`. Conclude with `(starGens P D).2.2.2.2.2`. Rewrite using `[hT]`. Simplify using the standard rewrite rules.
-/
theorem levelStar : LevelStar := by
  intro P D _ L h
  obtain ⟨-, -, -, -, -, -, hz, -, hzb, -, -, -, hn, hns, hT⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [hz, hzb]; exact (starGens P D).2.1
  · rw [hn, hns]; exact (starGens P D).2.2.2.2.2
  · rw [hT]; simp

def ioR : Matrix (Ty P) (Ty P) ℝ →+* A P D :=
  ((algebraMap ℂ D.Pr).comp Complex.ofRealHom).mapMatrix

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ioR_apply (Mt : Matrix (Ty P) (Ty P) ℝ) (a b : Ty P) :
    ioR P D Mt a b = algebraMap ℂ D.Pr ((Mt a b : ℝ) : ℂ) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_eq (f : Ty P → ℂ) : kap P D f = Matrix.diagonal fun π => algebraMap ℂ D.Pr (f π) := rfl

/- English proof (translation)
Use extensionality with `π' π`. Rewrite using `[ioR_apply]`. Simplify using `only [Mx4.sR, SS, Matrix.of_apply]`. Use `split_ifs`. Both sides reduce to the same expression.

Simplify using the standard rewrite rules.
-/
theorem ioR_sR (l : ℕ) : ioR P D (Mx4.sR P l) = SS P D l := by
  ext π' π
  rw [ioR_apply]
  simp only [Mx4.sR, SS, Matrix.of_apply]
  split_ifs
  · rfl
  · simp

/- English proof (translation)
Rewrite using `[kap_eq]`. Use extensionality with `a b`. Rewrite using `[ioR_apply]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.diagonal_apply_ne _ h]`.
-/
theorem ioR_diag (f : Ty P → ℝ) : ioR P D (Matrix.diagonal f) = kap P D fun π => ((f π : ℝ) : ℂ) := by
  rw [kap_eq]
  ext a b
  rw [ioR_apply]
  by_cases h : a = b
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.star_apply, ioR_apply, ioR_apply, Matrix.transpose_apply, ← algebraMap_star_comm]`. Simplify using the standard rewrite rules.
-/
theorem ioR_transpose (Mt : Matrix (Ty P) (Ty P) ℝ) : ioR P D Mt.transpose = star (ioR P D Mt) := by
  ext a b
  rw [Matrix.star_apply, ioR_apply, ioR_apply, Matrix.transpose_apply, ← algebraMap_star_comm]
  simp

/- English proof (translation)
Introduce `P D _ l w`. Use `show SS P D l * sc P D w = sc P D w * SS P D l`. Use extensionality with `π' π`. Simplify using `only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `(Algebra.commutes _ _)`. Simplify using the standard rewrite rules.
-/
theorem sSScalar : SSScalar := by
  intro P D _ l w
  show SS P D l * sc P D w = sc P D w * SS P D l
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

/- English proof (translation)
Introduce `P D _ l f g h`. Rewrite using `[kap_eq, kap_eq]`. Use extensionality with `π' π`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `hu : Up P l π π'`.

Simplify using `only [SS, Matrix.of_apply, if_pos hu, h π π' hu]`. Conclude with `(Algebra.commutes _ _)`. Simplify using `[SS, hu]`.
-/
theorem sSShift : SSShift := by
  intro P D _ l f g h
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]

/- English proof (translation)
Introduce `P D _ hP l hl`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← ioR_sR P D l, ← ioR_transpose, ← map_mul, Mx4.r_norm P hP l hl, ioR_diag]`. Rewrite using `[← ioR_sR P D l, ← ioR_transpose, ← map_mul, Mx4.r_normDown P hP l hl, ioR_diag]`.
-/
theorem sSNorm : SSNorm := by
  intro P D _ hP l hl
  constructor
  · rw [← ioR_sR P D l, ← ioR_transpose, ← map_mul, Mx4.r_norm P hP l hl, ioR_diag]
  · rw [← ioR_sR P D l, ← ioR_transpose, ← map_mul, Mx4.r_normDown P hP l hl, ioR_diag]

/- English proof (translation)
Introduce `P D _ hP l hl j hj hjl`. Establish `e1 : (kap P D fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) = ioR P D (Matrix.diagonal fun π => rho P π j - rho P π l - 1)` using `(ioR_diag P D _).symm`. Establish `e2 : (kap P D fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) = ioR P D (Matrix.diagonal fun π => rho P π j - rho P π l + 1)` using `(ioR_diag P D _).symm`. Rewrite using `[e1, e2, ← ioR_sR P D l, ← ioR_sR P D j]`. Simplify using `only [← map_mul]`.

Rewrite using `[Mx4.r_comm P hP l j hl hj hjl]`.
-/
theorem sSComm : SSComm := by
  intro P D _ hP l hl j hj hjl
  have e1 : (kap P D fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) =
      ioR P D (Matrix.diagonal fun π => rho P π j - rho P π l - 1) := (ioR_diag P D _).symm
  have e2 : (kap P D fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) =
      ioR P D (Matrix.diagonal fun π => rho P π j - rho P π l + 1) := (ioR_diag P D _).symm
  rw [e1, e2, ← ioR_sR P D l, ← ioR_sR P D j]
  simp only [← map_mul]
  rw [Mx4.r_comm P hP l j hl hj hjl]

/- English proof (translation)
Introduce `P D _ hP l hl j hj hjl`. Rewrite using `[← ioR_sR P D l, ← ioR_sR P D j, ← ioR_transpose]`. Simplify using `only [← map_mul]`. Rewrite using `[Mx4.r_mixed P hP l j hl hj hjl]`.
-/
theorem sSMixed : SSMixed := by
  intro P D _ hP l hl j hj hjl
  rw [← ioR_sR P D l, ← ioR_sR P D j, ← ioR_transpose]
  simp only [← map_mul]
  rw [Mx4.r_mixed P hP l j hl hj hjl]

/- English proof (translation)
Rewrite using `[Algebra.commutes c (Dd + (a : ℂ) • W), ← sub_mul]`. Use `congr 1`. Use `push_cast`. Rewrite using `[sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem nab_step (a : ℝ) (Dd W : D.Pr) (c : ℂ) :
    (Dd + ((a - 1 : ℝ) : ℂ) • W) * algebraMap ℂ D.Pr c =
      algebraMap ℂ D.Pr c * (Dd + (a : ℂ) • W) - W * algebraMap ℂ D.Pr c := by
  rw [Algebra.commutes c (Dd + (a : ℂ) • W), ← sub_mul]
  congr 1
  push_cast
  rw [sub_smul, one_smul]
  abel

/- English proof (translation)
Introduce `P D _ l hl`. Prove the components needed by the constructor for the conclusion. Use extensionality with `π' π`. Simplify using `only [nabA, zbA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply]`. Distinguish the cases in `hU : Up P l π π'`.

Simplify using `only [SS, Matrix.of_apply, if_pos hU]`. Rewrite using `[Mx4.aC_up P l hl π π' hU]`. Conclude with `nab_step P D _ _ _ _`. Simplify using `only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]`. Use extensionality with `π' π`.

Simplify using `only [nabsA, zA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.sub_apply]`. Distinguish the cases in `hU : Up P l π π'`. Simplify using `only [SS, Matrix.of_apply, if_pos hU]`. Rewrite using `[Mx4.aC_up P l hl π π' hU]`. Conclude with `nab_step P D _ _ _ _`.

Simplify using `only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]`.
-/
theorem nabSS : NabSS := by
  intro P D _ l hl
  constructor
  · ext π' π
    simp only [nabA, zbA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.sub_apply]
    by_cases hU : Up P l π π'
    · simp only [SS, Matrix.of_apply, if_pos hU]
      rw [Mx4.aC_up P l hl π π' hU]
      exact nab_step P D _ _ _ _
    · simp only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]
  · ext π' π
    simp only [nabsA, zA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.sub_apply]
    by_cases hU : Up P l π π'
    · simp only [SS, Matrix.of_apply, if_pos hU]
      rw [Mx4.aC_up P l hl π π' hU]
      exact nab_step P D _ _ _ _
    · simp only [SS, Matrix.of_apply, if_neg hU, mul_zero, zero_mul, sub_zero]

/- English proof (translation)
Introduce `P D _`. Establish `hL : D.Laws P.TT` using `Fact.out`. Rewrite using `[kap_eq]`. Simplify using `only [nabA, nabsA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]`. Use `congr 1`.

Use function extensionality and compare the values at `π`. Conclude with `curv hL _`.
-/
theorem curvature : Curvature := by
  intro P D _
  have hL : D.Laws P.TT := Fact.out
  rw [kap_eq]
  simp only [nabA, nabsA, ggiA, sc, Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_sub]
  congr 1
  funext π
  exact curv hL _

end Mat

end

end Formalism.FourierDecayAlt.P.MAx1

end

section

open  Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx1.D5

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_eq (f : Ty P → ℂ) :
    kap P D f = Matrix.diagonal fun π => algebraMap ℂ (D.Pr) (f π) := rfl

/- English proof (translation)
Use `show kap P D f * Matrix.diagonal d = Matrix.diagonal d * kap P D f`. Rewrite using `[kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `Algebra.commutes _ _`.
-/
theorem kap_diag (f : Ty P → ℂ) (d : Ty P → D.Pr) :
    Commute (kap P D f) (Matrix.diagonal d) := by
  show kap P D f * Matrix.diagonal d = Matrix.diagonal d * kap P D f
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1; funext π; exact Algebra.commutes _ _

/- English proof (translation)
The claim follows from `kap_diag P D f _`.
-/
theorem kap_sc (f : Ty P → ℂ) (w : D.Pr) : Commute (kap P D f) (sc P D w) := kap_diag P D f _

/- English proof (translation)
The claim follows from `kap_diag P D f _`.
-/
theorem kap_kap (f g : Ty P → ℂ) : Commute (kap P D f) (kap P D g) := kap_diag P D f _

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `(algebraMap_star_comm (f π)).symm`.
-/
theorem star_kap (f : Ty P → ℂ) : star (kap P D f) = kap P D fun π => star (f π) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1; funext π
  exact (algebraMap_star_comm (f π)).symm

/- English proof (translation)
The claim follows from `(kap P D).commutes c`.
-/
theorem kap_const (c : ℂ) : (kap P D fun _ => c) = algebraMap ℂ (A P D) c := (kap P D).commutes c

/- English proof (translation)
The claim follows from `map_mul (kap P D) f g`.
-/
theorem kap_mul (f g : Ty P → ℂ) : (kap P D fun π => f π * g π) = kap P D f * kap P D g :=
  map_mul (kap P D) f g

/- English proof (translation)
The claim follows from `map_add (kap P D) f g`.
-/
theorem kap_add (f g : Ty P → ℂ) : (kap P D fun π => f π + g π) = kap P D f + kap P D g :=
  map_add (kap P D) f g

/- English proof (translation)
The claim follows from `map_smul (kap P D) c f`.
-/
theorem kap_smul (c : ℂ) (f : Ty P → ℂ) : (kap P D fun π => c * f π) = c • kap P D f :=
  map_smul (kap P D) c f

/- English proof (translation)
Rewrite using `[← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using the standard rewrite rules.
-/
theorem kap_sum {ι : Type} (s : Finset ι) (f : ι → Ty P → ℂ) :
    (kap P D fun π => ∑ i ∈ s, f i π) = ∑ i ∈ s, kap P D (f i) := by
  rw [← map_sum]; congr 1; funext π; simp

/- English proof (translation)
Use `show SS P D l * sc P D w = sc P D w * SS P D l`. Use extensionality with `π' π`. Simplify using `only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]`. Use `split_ifs`. Conclude with `(Algebra.commutes _ _)`.

Simplify using the standard rewrite rules.
-/
theorem ss_sc (l : ℕ) (w : D.Pr) : Commute (SS P D l) (sc P D w) := by
  show SS P D l * sc P D w = sc P D w * SS P D l
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

/- English proof (translation)
Establish `h` using `(ss_sc P D l (star w)).star_star`. Rewrite `h` using `[star_sc, star_star]`. Then use the resulting hypothesis.
-/
theorem sss_sc (l : ℕ) (w : D.Pr) : Commute (star (SS P D l)) (sc P D w) := by
  have h := (ss_sc P D l (star w)).star_star
  rwa [star_sc, star_star] at h

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq]`. Use extensionality with `π' π`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `hu : Up P l π π'`. Simplify using `only [SS, Matrix.of_apply, if_pos hu, h π π' hu]`.

Conclude with `(Algebra.commutes _ _)`. Simplify using `[SS, hu]`.
-/
theorem ss_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    kap P D g * SS P D l = SS P D l * kap P D f := by
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]

/- English proof (translation)
Establish `h1` using `ss_shift P D l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])`. Establish `h2` using `congrArg star h1`. Rewrite `h2` using `[star_mul, star_mul, star_kap, star_kap]`. Simplify using `using h2`.
-/
theorem sss_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P D l) * kap P D g = kap P D f * star (SS P D l) := by
  have h1 := ss_shift P D l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa using h2

/- English proof (translation)
The claim follows from `(map_mul (Matrix.scalar (Ty P)) w w').symm`.
-/
theorem sc_mul (w w' : D.Pr) : sc P D w * sc P D w' = sc P D (w * w') :=
  (map_mul (Matrix.scalar (Ty P)) w w').symm

/- English proof (translation)
Use `show _ * _ = _ * _`. Rewrite using `[sc_mul, sc_mul, multiplierPair_comm D]`.
-/
theorem fn_comm (f fb g gb : D.R) : Commute (sc P D (D.fnP f fb)) (sc P D (D.fnP g gb)) := by
  show _ * _ = _ * _
  rw [sc_mul, sc_mul, multiplierPair_comm D]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, h, -, -⟩` from `levFns P D`. Conclude with `h`.
-/
theorem gg_ggi : ggA P D * ggiA P D = 1 := by
  obtain ⟨-, -, -, -, -, -, h, -, -⟩ := levFns P D; exact h
/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, h, -⟩` from `levFns P D`. Conclude with `h`.
-/
theorem ggi_gg : ggiA P D * ggA P D = 1 := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := levFns P D; exact h
/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, h⟩` from `levFns P D`. Conclude with `h`.
-/
theorem gg_def : ggA P D = zA P D * zbA P D - algebraMap ℂ (A P D) (P.TT : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := levFns P D; exact h
/- English proof (translation)
The claim follows from `(levNab P D).1`.
-/
theorem nabla_zeta_comm : nabA P D * zA P D = zA P D * nabA P D + 1 := (levNab P D).1
/- English proof (translation)
Take `⟨-, -, -, -, h, -, -⟩` from `levNab P D`. Conclude with `h`.
-/
theorem nab_gg : nabA P D * ggA P D = ggA P D * nabA P D + zbA P D := by
  obtain ⟨-, -, -, -, h, -, -⟩ := levNab P D; exact h
/- English proof (translation)
Take `⟨-, -, h, -, -, -, -⟩` from `levNabs P D`. Conclude with `h`.
-/
theorem nabs_alt : nabsA P D * zA P D = zA P D * nabsA P D := by
  obtain ⟨-, -, h, -, -, -, -⟩ := levNabs P D; exact h
/- English proof (translation)
Take `⟨-, -, -, -, h, -, -⟩` from `levNabs P D`. Conclude with `h`.
-/
theorem nabs_gg : nabsA P D * ggA P D = ggA P D * nabsA P D - zA P D := by
  obtain ⟨-, -, -, -, h, -, -⟩ := levNabs P D; exact h
/- English proof (translation)
The claim follows from `(starGens P D).2.1`.
-/
theorem star_alt : star (zA P D) = zbA P D := (starGens P D).2.1
/- English proof (translation)
Rewrite using `[← star_alt, star_star]`.
-/
theorem star_zb : star (zbA P D) = zA P D := by rw [← star_alt, star_star]
/- English proof (translation)
The claim follows from `(starGens P D).2.2.2.1`.
-/
theorem star_gg : star (ggA P D) = ggA P D := (starGens P D).2.2.2.1
/- English proof (translation)
The claim follows from `(starGens P D).2.2.2.2.1`.
-/
theorem star_ggi : star (ggiA P D) = ggiA P D := (starGens P D).2.2.2.2.1
/- English proof (translation)
The claim follows from `(starGens P D).2.2.2.2.2`.
-/
theorem star_nab : star (nabA P D) = nabsA P D := (starGens P D).2.2.2.2.2
/- English proof (translation)
Rewrite using `[← star_nab, star_star]`.
-/
theorem star_nabs : star (nabsA P D) = nabA P D := by rw [← star_nab, star_star]

/- English proof (translation)
Rewrite using `[l0A, Algebra.smul_def]`.
-/
theorem l0_eq_neg_nabla_sub (Y : ℂ) : l0A P D Y = -nabA P D - (Y + 1 / 2) • (zbA P D * ggiA P D) := by
  rw [l0A, Algebra.smul_def]
/- English proof (translation)
Rewrite using `[m0A, Algebra.smul_def]`.
-/
theorem raising_constant_eq_nabla_star (Y : ℂ) : m0A P D Y = -nabsA P D - (Y - 1 / 2) • (zA P D * ggiA P D) := by
  rw [m0A, Algebra.smul_def]

/- English proof (translation)
Establish `h : Commute (zbA P D * ggiA P D) (zA P D)` using `(fn_comm P D _ _ _ _).mul_left (fn_comm P D _ _ _ _)`. Rewrite using `[l0_eq_neg_nabla_sub, sub_mul, mul_sub, neg_mul, mul_neg, nabla_zeta_comm, smul_mul_assoc, mul_smul_comm, h.eq]`. Normalize the expressions using the abelian group laws.
-/
theorem lowering_constant_zeta_comm (Y : ℂ) : l0A P D Y * zA P D = zA P D * l0A P D Y - 1 := by
  have h : Commute (zbA P D * ggiA P D) (zA P D) := (fn_comm P D _ _ _ _).mul_left (fn_comm P D _ _ _ _)
  rw [l0_eq_neg_nabla_sub, sub_mul, mul_sub, neg_mul, mul_neg, nabla_zeta_comm, smul_mul_assoc, mul_smul_comm, h.eq]
  abel

/- English proof (translation)
Rewrite using `[raising_constant_eq_nabla_star]`. Conclude with `((show Commute (nabsA P D) (zA P D) from nabs_alt P D).neg_left).sub_left (((fn_comm P D _ _ _ _).mul_left (fn_comm P D _ _ _ _)).smul_left _)`.
-/
theorem raising_constant_commute_zeta (Y : ℂ) : Commute (m0A P D Y) (zA P D) := by
  rw [raising_constant_eq_nabla_star]
  exact ((show Commute (nabsA P D) (zA P D) from nabs_alt P D).neg_left).sub_left
    (((fn_comm P D _ _ _ _).mul_left (fn_comm P D _ _ _ _)).smul_left _)

/- English proof (translation)
Unfold `weightedSumBis`. Conclude with `Commute.sum_left _ _ _ fun l _ => (ss_sc P D l w).mul_left (kap_sc P D _ w)`.
-/
theorem S21_commute_scalar (Y : ℂ) (w : D.Pr) : Commute (weightedSumBis P D Y) (sc P D w) := by
  unfold weightedSumBis
  exact Commute.sum_left _ _ _ fun l _ => (ss_sc P D l w).mul_left (kap_sc P D _ w)

/- English proof (translation)
Unfold `S12`. Conclude with `Commute.sum_left _ _ _ fun l _ => (kap_sc P D _ w).mul_left (sss_sc P D l w)`.
-/
theorem upper_sum_commute_scalar (Y : ℂ) (w : D.Pr) : Commute (S12 P D Y) (sc P D w) := by
  unfold S12
  exact Commute.sum_left _ _ _ fun l _ => (kap_sc P D _ w).mul_left (sss_sc P D l w)

/- English proof (translation)
Unfold `S4`. Conclude with `Commute.sum_left _ _ _ fun l _ => Commute.sum_left _ _ _ fun j _ => ((sss_sc P D l w).mul_left (ss_sc P D j w)).mul_left (kap_sc P D _ w)`.
-/
theorem quartic_sum_commute_scalar (Y : ℂ) (w : D.Pr) : Commute (S4 P D Y) (sc P D w) := by
  unfold S4
  exact Commute.sum_left _ _ _ fun l _ => Commute.sum_left _ _ _ fun j _ =>
    ((sss_sc P D l w).mul_left (ss_sc P D j w)).mul_left (kap_sc P D _ w)

/- English proof (translation)
Establish `h1 : B * l * z = z * (B * l) - B`. Rewrite using `[mul_assoc, hl, mul_sub, mul_one, ← mul_assoc, hB.eq, mul_assoc]`. Establish `h2 : D * l * z = z * (D * l) - D`. Rewrite using `[mul_assoc, hl, mul_sub, mul_one, ← mul_assoc, hD.eq, mul_assoc]`. Simplify using `only [add_mul, mul_add, h1, h2, ha.eq, hc.eq, he.eq]`.

Normalize the expressions using the abelian group laws.
-/
theorem commGroup_mul_eq_mul_mul_div {R : Type*} [Ring R] (a B c D e l z : R) (ha : Commute a z) (hB : Commute B z)
    (hc : Commute c z) (hD : Commute D z) (he : Commute e z) (hl : l * z = z * l - 1) :
    (a + B * l + c + D * l + e) * z - z * (a + B * l + c + D * l + e) = -(B + D) := by
  have h1 : B * l * z = z * (B * l) - B := by
    rw [mul_assoc, hl, mul_sub, mul_one, ← mul_assoc, hB.eq, mul_assoc]
  have h2 : D * l * z = z * (D * l) - D := by
    rw [mul_assoc, hl, mul_sub, mul_one, ← mul_assoc, hD.eq, mul_assoc]
  simp only [add_mul, mul_add, h1, h2, ha.eq, hc.eq, he.eq]
  abel

/- English proof (translation)
Introduce `P D _ Y`. Establish `hgx : Commute (ggA P D * xA P D Y) (zA P D)` using `(fn_comm P D _ _ _ _).mul_left (kap_sc P D _ _)`. Use `⟨?_, ?_, ?_, hgx⟩` and prove the remaining obligations. Establish `h` using `commGroup_mul_eq_mul_mul_div 0 (ggA P D * xA P D Y) (weightedSumBis P D Y) 0 0 (l0A P D Y) (zA P D) (Commute.zero_left _) hgx (S21_commute_scalar P D Y _) (Commute.zero_left _) (Commute.zero_left _) (lowering_constant_zeta_comm P D Y)`. Simplify `h` using `[t21, t22]`.

Establish `h` using `commGroup_mul_eq_mul_mul_div (ggiA P D * (kap P D fun π => wC P π Y)) (ggA P D * xA P D Y * m0A P D Y) (ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y) (S12 P D Y) (ggiA P D * S4 P D Y) (l0A P D Y) (zA P D) ((fn_comm P D _ _ _ _).mul_left (kap_sc P D _ _)) (hgx.mul_left (r …`. Conclude with `h`. Conclude with `(hgx.mul_left (raising_constant_commute_zeta P D Y)).add_left (upper_sum_commute_scalar P D Y _)`.
-/
theorem qQZeta : QQZeta := by
  intro P D _ Y
  have hgx : Commute (ggA P D * xA P D Y) (zA P D) := (fn_comm P D _ _ _ _).mul_left (kap_sc P D _ _)
  refine ⟨?_, ?_, ?_, hgx⟩
  · have h := commGroup_mul_eq_mul_mul_div 0 (ggA P D * xA P D Y) (weightedSumBis P D Y) 0 0 (l0A P D Y) (zA P D) (Commute.zero_left _) hgx
      (S21_commute_scalar P D Y _) (Commute.zero_left _) (Commute.zero_left _) (lowering_constant_zeta_comm P D Y)
    simpa [t21, t22] using h
  · have h := commGroup_mul_eq_mul_mul_div (ggiA P D * (kap P D fun π => wC P π Y)) (ggA P D * xA P D Y * m0A P D Y)
      (ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y) (S12 P D Y) (ggiA P D * S4 P D Y) (l0A P D Y) (zA P D)
      ((fn_comm P D _ _ _ _).mul_left (kap_sc P D _ _)) (hgx.mul_left (raising_constant_commute_zeta P D Y))
      ((((fn_comm P D _ _ _ _).mul_left (raising_constant_commute_zeta P D Y)).mul_left (fn_comm P D _ _ _ _)).mul_left (S21_commute_scalar P D Y _))
      (upper_sum_commute_scalar P D Y _) ((fn_comm P D _ _ _ _).mul_left (quartic_sum_commute_scalar P D Y _)) (lowering_constant_zeta_comm P D Y)
    exact h
  · exact (hgx.mul_left (raising_constant_commute_zeta P D Y)).add_left (upper_sum_commute_scalar P D Y _)

/- English proof (translation)
Establish `h2 : g * N = N * g + e • z` using `by rw [hN]; abel`. Establish `h3 : g * N * gi = N + e • (gi * z)`. Rewrite using `[h2, add_mul, mul_assoc, h1, mul_one, smul_mul_assoc, hzgi.eq]`. Establish `h4 : g * (z * gi) * gi = gi * z`. Rewrite using `[← mul_assoc, ← hzg.eq, mul_assoc z g gi, h1, mul_one, hzgi.eq]`.

Rewrite using `[mul_sub, sub_mul, mul_neg, neg_mul, h3, mul_smul_comm, smul_mul_assoc, h4, add_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem block_frame_conjugation_identity {R : Type*} [Ring R] [Algebra ℂ R] (g gi z N : R) (a e : ℂ) (h1 : g * gi = 1)
    (hN : N * g = g * N - e • z) (hzg : Commute z g) (hzgi : Commute z gi) :
    g * (-N - a • (z * gi)) * gi = -N - (a + e) • (gi * z) := by
  have h2 : g * N = N * g + e • z := by rw [hN]; abel
  have h3 : g * N * gi = N + e • (gi * z) := by
    rw [h2, add_mul, mul_assoc, h1, mul_one, smul_mul_assoc, hzgi.eq]
  have h4 : g * (z * gi) * gi = gi * z := by
    rw [← mul_assoc, ← hzg.eq, mul_assoc z g gi, h1, mul_one, hzgi.eq]
  rw [mul_sub, sub_mul, mul_neg, neg_mul, h3, mul_smul_comm, smul_mul_assoc, h4, add_smul]
  abel

/- English proof (translation)
Establish `h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ)` using `by norm_num`. Rewrite using `[h, Complex.star_def, Complex.conj_ofReal]`.
-/
theorem star_half : star (1 / 2 : ℂ) = 1 / 2 := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Establish `h : (2 : ℂ) = ((2 : ℝ) : ℂ)` using `by norm_num`. Rewrite using `[h, Complex.conj_ofReal]`.
-/
theorem conj_two : (starRingEnd ℂ) 2 = 2 := by
  have h : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [h, Complex.conj_ofReal]

/- English proof (translation)
Rewrite using `[raising_constant_eq_nabla_star, block_frame_conjugation_identity (ggA P D) (ggiA P D) (zA P D) (nabsA P D) (star Y - 1 / 2) 1 (gg_ggi P D) (by rw [one_smul]; exact nabs_gg P D) (fn_comm P D _ _ _ _) (fn_comm P D _ _ _ _), l0_eq_neg_nabla_sub, star_sub, star_neg, star_smul, star_ …`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_lowering_constant (Y : ℂ) : star (l0A P D Y) = ggA P D * m0A P D (star Y) * ggiA P D := by
  rw [raising_constant_eq_nabla_star, block_frame_conjugation_identity (ggA P D) (ggiA P D) (zA P D) (nabsA P D) (star Y - 1 / 2) 1 (gg_ggi P D)
    (by rw [one_smul]; exact nabs_gg P D) (fn_comm P D _ _ _ _) (fn_comm P D _ _ _ _), l0_eq_neg_nabla_sub,
    star_sub, star_neg, star_smul, star_mul, star_nab, star_zb, star_ggi, star_add, star_half]
  congr 2; ring

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub, block_frame_conjugation_identity (ggA P D) (ggiA P D) (zbA P D) (nabA P D) (star Y + 1 / 2) (-1) (gg_ggi P D) (by rw [neg_smul, one_smul, sub_neg_eq_add]; exact nab_gg P D) (fn_comm P D _ _ _ _) (fn_comm P D _ _ _ _), raising_constant_eq_nabla_star, star_sub …`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_raising_constant (Y : ℂ) : star (m0A P D Y) = ggA P D * l0A P D (star Y) * ggiA P D := by
  rw [l0_eq_neg_nabla_sub, block_frame_conjugation_identity (ggA P D) (ggiA P D) (zbA P D) (nabA P D) (star Y + 1 / 2) (-1) (gg_ggi P D)
    (by rw [neg_smul, one_smul, sub_neg_eq_add]; exact nab_gg P D) (fn_comm P D _ _ _ _) (fn_comm P D _ _ _ _),
    raising_constant_eq_nabla_star, star_sub, star_neg, star_smul, star_mul, star_nabs, star_alt, star_ggi, star_sub, star_half]
  congr 2; ring

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub]`. Conclude with `((kap_diag P D f _).neg_right).sub_right (((kap_sc P D f _).mul_right (kap_sc P D f _)).smul_right _)`.
-/
theorem kappa_commute_l0 (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P D f) (l0A P D Y) := by
  rw [l0_eq_neg_nabla_sub]
  exact ((kap_diag P D f _).neg_right).sub_right (((kap_sc P D f _).mul_right (kap_sc P D f _)).smul_right _)

/- English proof (translation)
Rewrite using `[raising_constant_eq_nabla_star]`. Conclude with `((kap_diag P D f _).neg_right).sub_right (((kap_sc P D f _).mul_right (kap_sc P D f _)).smul_right _)`.
-/
theorem kappa_commute_raising_constant (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P D f) (m0A P D Y) := by
  rw [raising_constant_eq_nabla_star]
  exact ((kap_diag P D f _).neg_right).sub_right (((kap_sc P D f _).mul_right (kap_sc P D f _)).smul_right _)

/- English proof (translation)
Unfold `xEx`. Rewrite using `[star_prod]`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_add, Complex.star_def, Complex.conj_ofReal]`.
-/
theorem star_xEx (ex : Finset ℕ) (π : Ty P) (Y : ℂ) : star (xEx P ex π Y) = xEx P ex π (star Y) := by
  unfold xEx
  rw [star_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [star_add, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Unfold `xC`. Rewrite using `[star_prod]`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[star_add, Complex.star_def, Complex.conj_ofReal]`.
-/
theorem star_xC (π : Ty P) (Y : ℂ) : star (xC P π Y) = xC P π (star Y) := by
  unfold xC
  rw [star_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [star_add, Complex.star_def, Complex.conj_ofReal]

/- English proof (translation)
Unfold `xA`. Rewrite using `[star_kap]`. Simplify using `only [star_xC]`.
-/
theorem star_xA (Y : ℂ) : star (xA P D Y) = xA P D (star Y) := by
  unfold xA
  rw [star_kap]; simp only [star_xC]

/- English proof (translation)
Unfold `weightedSumBis S12`. Rewrite using `[star_sum]`. Use `sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul, star_kap]`. Simplify using `only [star_xEx]`.
-/
theorem star_lower_sum (Y : ℂ) : star (weightedSumBis P D Y) = S12 P D (star Y) := by
  unfold weightedSumBis S12
  rw [star_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [star_mul, star_kap]; simp only [star_xEx]

/- English proof (translation)
Unfold `weightedSumBis S12`. Rewrite using `[star_sum]`. Use `sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul, star_kap, star_star]`. Simplify using `only [star_xEx]`.
-/
theorem star_upper_sum (Y : ℂ) : star (S12 P D Y) = weightedSumBis P D (star Y) := by
  unfold weightedSumBis S12
  rw [star_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [star_mul, star_kap, star_star]; simp only [star_xEx]

/- English proof (translation)
Unfold `xEx`. Use `prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[mem_sdiff]`. Rewrite using `[rho_raise P l π π' h i hi.1, if_neg (by rintro rfl; exact hi.2 hl)]`. Simplify using the standard rewrite rules.
-/
theorem xEx_up (l : ℕ) (ex : Finset ℕ) (hl : l ∈ ex) (Y : ℂ) (π π' : Ty P) (h : Up P l π π') :
    xEx P ex π' Y = xEx P ex π Y := by
  unfold xEx
  refine prod_congr rfl fun i hi => ?_
  rw [mem_sdiff] at hi
  rw [rho_raise P l π π' h i hi.1, if_neg (by rintro rfl; exact hi.2 hl)]
  simp

/- English proof (translation)
The claim follows from `ss_shift P D l f f h`.
-/
theorem kap_ss (l : ℕ) (f : Ty P → ℂ) (h : ∀ π π', Up P l π π' → f π' = f π) :
    Commute (kap P D f) (SS P D l) := ss_shift P D l f f h

/- English proof (translation)
The claim follows from `(sss_shift P D l f f h).symm`.
-/
theorem kap_sss (l : ℕ) (f : Ty P → ℂ) (h : ∀ π π', Up P l π π' → f π' = f π) :
    Commute (kap P D f) (star (SS P D l)) := (sss_shift P D l f f h).symm

/- English proof (translation)
Unfold `S4`. Simplify using `only [star_sum]`. Rewrite using `[Finset.sum_comm' (s' := fun y => (Icc 1 (P.k - 1)).erase y) (t' := Icc 1 (P.k - 1)) (fun x y => by`. Simplify using `only [mem_erase]`. Conclude with `⟨fun ⟨a, b, c⟩ => ⟨⟨b.symm, a⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨b, a.symm, c⟩⟩)]`.

Use `sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul, star_mul, star_star, star_kap]`. Simplify using `only [star_xEx]`. Rewrite using `[Finset.pair_comm l j]`. Conclude with `((kap_sss P D j _ (xEx_up P j _ (by simp) _)).mul_right (kap_ss P D l _ (xEx_up P l _ (by simp) _))).eq`.
-/
theorem star_quartic_sum (Y : ℂ) : star (S4 P D Y) = S4 P D (star Y) := by
  unfold S4
  simp only [star_sum]
  rw [Finset.sum_comm' (s' := fun y => (Icc 1 (P.k - 1)).erase y) (t' := Icc 1 (P.k - 1))
    (fun x y => by
      simp only [mem_erase]
      exact ⟨fun ⟨a, b, c⟩ => ⟨⟨b.symm, a⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨b, a.symm, c⟩⟩)]
  refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
  rw [star_mul, star_mul, star_star, star_kap]
  simp only [star_xEx]
  rw [Finset.pair_comm l j]
  exact ((kap_sss P D j _ (xEx_up P j _ (by simp) _)).mul_right (kap_ss P D l _ (xEx_up P l _ (by simp) _))).eq

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _`.
-/
theorem coordinate_polynomial_monic (π : Ty P) : (coordinatePolynomial P π).Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

/- English proof (translation)
Establish `h1 : (wNum P π).map (starRingEnd ℂ) = wNum P π`. Simplify using `[wNum, qP, Polynomial.map_sum, Polynomial.map_prod, conj_two]`. Establish `h2 : (coordinatePolynomial P π).map (starRingEnd ℂ) = coordinatePolynomial P π` using `by simp [coordinatePolynomial, Polynomial.map_prod]`. Establish `h3 : (wNum P π /ₘ coordinatePolynomial P π).map (starRingEnd ℂ) = wNum P π /ₘ coordinatePolynomial P π`. Rewrite using `[Polynomial.map_divByMonic _ (coordinate_polynomial_monic P π), h1, h2]`.

Use `show (starRingEnd ℂ) ((wNum P π /ₘ coordinatePolynomial P π).eval Y) = (wNum P π /ₘ coordinatePolynomial P π).eval ((starRingEnd ℂ) Y)`. Rewrite using `[← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h3]`.
-/
theorem star_wC (π : Ty P) (Y : ℂ) : star (wC P π Y) = wC P π (star Y) := by
  have h1 : (wNum P π).map (starRingEnd ℂ) = wNum P π := by
    simp [wNum, qP, Polynomial.map_sum, Polynomial.map_prod, conj_two]
  have h2 : (coordinatePolynomial P π).map (starRingEnd ℂ) = coordinatePolynomial P π := by simp [coordinatePolynomial, Polynomial.map_prod]
  have h3 : (wNum P π /ₘ coordinatePolynomial P π).map (starRingEnd ℂ) = wNum P π /ₘ coordinatePolynomial P π := by
    rw [Polynomial.map_divByMonic _ (coordinate_polynomial_monic P π), h1, h2]
  show (starRingEnd ℂ) ((wNum P π /ₘ coordinatePolynomial P π).eval Y) = (wNum P π /ₘ coordinatePolynomial P π).eval ((starRingEnd ℂ) Y)
  rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, h3]

/- English proof (translation)
The claim follows from `(kap_sc P D f _).eq`.
-/
theorem kap_ggi (f : Ty P → ℂ) : kap P D f * ggiA P D = ggiA P D * kap P D f := (kap_sc P D f _).eq
/- English proof (translation)
The claim follows from `(kap_sc P D f _).eq`.
-/
theorem kap_gg (f : Ty P → ℂ) : kap P D f * ggA P D = ggA P D * kap P D f := (kap_sc P D f _).eq
/- English proof (translation)
The claim follows from `(quartic_sum_commute_scalar P D Y _).eq`.
-/
theorem quartic_sum_gamma_inv_comm (Y : ℂ) : S4 P D Y * ggiA P D = ggiA P D * S4 P D Y := (quartic_sum_commute_scalar P D Y _).eq

/- English proof (translation)
Rewrite using `[← mul_assoc, ← kap_ggi, mul_assoc, ggi_gg, mul_one]`.
-/
theorem ggi_kap_gg (f : Ty P → ℂ) : ggiA P D * (kap P D f * ggA P D) = kap P D f := by
  rw [← mul_assoc, ← kap_ggi, mul_assoc, ggi_gg, mul_one]

/- English proof (translation)
Unfold `t22`. Rewrite using `[star_mul, star_xA, star_gg]`. Conclude with `(kap_sc P D _ _).eq`.
-/
theorem star_t22 (Y : ℂ) : star (t22 P D Y) = t22 P D (star Y) := by
  unfold t22
  rw [star_mul, star_xA, star_gg]
  exact (kap_sc P D _ _).eq

/- English proof (translation)
Unfold `t21 t12`. Rewrite using `[star_add, star_mul, star_mul, star_lower_sum, star_lowering_constant, star_xA, star_gg]`. Establish `h : ggA P D * m0A P D (star Y) * ggiA P D * (xA P D (star Y) * ggA P D) = ggA P D * xA P D (star Y) * m0A P D (star Y)`. Rewrite using `[mul_assoc _ (ggiA P D), xA, ggi_kap_gg, mul_assoc, ← (kappa_commute_raising_constant P D _ _).eq, mul_assoc]`. Rewrite using `[h]`.
-/
theorem star_t21 (Y : ℂ) : star (t21 P D Y) = t12 P D (star Y) := by
  unfold t21 t12
  rw [star_add, star_mul, star_mul, star_lower_sum, star_lowering_constant, star_xA, star_gg]
  have h : ggA P D * m0A P D (star Y) * ggiA P D * (xA P D (star Y) * ggA P D) =
      ggA P D * xA P D (star Y) * m0A P D (star Y) := by
    rw [mul_assoc _ (ggiA P D), xA, ggi_kap_gg, mul_assoc, ← (kappa_commute_raising_constant P D _ _).eq, mul_assoc]
  rw [h]

/- English proof (translation)
Establish `h` using `star_t21 P D (star Y)`. Rewrite `h` using `[star_star]`. Rewrite using `[← h, star_star]`.
-/
theorem star_t12 (Y : ℂ) : star (t12 P D Y) = t21 P D (star Y) := by
  have h := star_t21 P D (star Y)
  rw [star_star] at h
  rw [← h, star_star]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = g * M * L * x := by rw [h2, mul_one, e1]`. Use `_ = g * (M * L * x) := by simp only [mul_assoc]`. Use `_ = g * (x * (M * L)) := by rw [(hxM.mul_right hxL).eq]`.

Use `_ = g * x * M * L := by simp only [mul_assoc]`.
-/
theorem conj_eq_of_nonneg_real {R : Type*} [Ring R] (g gi x M L : R) (h2 : gi * g = 1)
    (e1 : gi * (x * g) = x) (hxM : Commute x M) (hxL : Commute x L) :
    g * M * gi * (g * L * gi * (x * g)) = g * x * M * L := by
  calc g * M * gi * (g * L * gi * (x * g)) = g * M * (gi * g) * L * (gi * (x * g)) := by
        simp only [mul_assoc]
    _ = g * M * L * x := by rw [h2, mul_one, e1]
    _ = g * (M * L * x) := by simp only [mul_assoc]
    _ = g * (x * (M * L)) := by rw [(hxM.mul_right hxL).eq]
    _ = g * x * M * L := by simp only [mul_assoc]

/- English proof (translation)
Unfold `t11`. Simplify using `only [star_add, star_mul, star_lower_sum, star_upper_sum, star_quartic_sum, star_lowering_constant, star_raising_constant, star_xA, star_gg, star_ggi, star_kap, star_wC]`. Rewrite using `[conj_eq_of_nonneg_real (ggA P D) (ggiA P D) (xA P D (star Y)) (m0A P D (star Y)) (l0A P D (star Y)) (ggi_gg P D) (ggi_kap_gg P D _) (kappa_commute_raising_constant P D _ _) (kappa_commute_l0 P D _ _), kap_ggi, quartic_sum_gamma_inv_comm]`. Establish `h : S12 P D (star Y) * (ggiA P D * (ggA P D * l0A P D (star Y) * ggiA P D * ggA P D)) = S12 P D (star Y) * l0A P D (star Y)`. Use `congr 1`.

Rewrite using `[mul_assoc (ggA P D * l0A P D (star Y)), ggi_gg, mul_one, ← mul_assoc, ggi_gg, one_mul]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem star_t11 (Y : ℂ) : star (t11 P D Y) = t11 P D (star Y) := by
  unfold t11
  simp only [star_add, star_mul, star_lower_sum, star_upper_sum, star_quartic_sum, star_lowering_constant, star_raising_constant, star_xA, star_gg,
    star_ggi, star_kap, star_wC]
  rw [conj_eq_of_nonneg_real (ggA P D) (ggiA P D) (xA P D (star Y)) (m0A P D (star Y)) (l0A P D (star Y)) (ggi_gg P D)
    (ggi_kap_gg P D _) (kappa_commute_raising_constant P D _ _) (kappa_commute_l0 P D _ _), kap_ggi, quartic_sum_gamma_inv_comm]
  have h : S12 P D (star Y) * (ggiA P D * (ggA P D * l0A P D (star Y) * ggiA P D * ggA P D)) =
      S12 P D (star Y) * l0A P D (star Y) := by
    congr 1
    rw [mul_assoc (ggA P D * l0A P D (star Y)), ggi_gg, mul_one, ← mul_assoc, ggi_gg, one_mul]
  rw [h]
  abel

/- English proof (translation)
Introduce `P D _ _ Y`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `congrFun (congrFun (star_t11 P D Y) _) _`. Conclude with `congrFun (congrFun (star_t21 P D Y) _) _`.

Conclude with `congrFun (congrFun (star_t12 P D Y) _) _`. Conclude with `congrFun (congrFun (star_t22 P D Y) _) _`.
-/
theorem qQHerm : QQHerm := by
  intro P D _ _ Y
  ext i j
  fin_cases i <;> fin_cases j
  · exact congrFun (congrFun (star_t11 P D Y) _) _
  · exact congrFun (congrFun (star_t21 P D Y) _) _
  · exact congrFun (congrFun (star_t12 P D Y) _) _
  · exact congrFun (congrFun (star_t22 P D Y) _) _

section lead

variable {R : Type*} [Ring R] [Algebra ℂ R]

def Lead (n : ℕ) (c : R) (f : ℂ → R) : Prop :=
  ∃ a : ℕ → R, ∀ Y, f Y = Y ^ n • c + ∑ i ∈ range n, Y ^ i • a i

/- English proof (translation)
Rewrite using `[← map_pow, ← Algebra.commutes, ← Algebra.smul_def]`.
-/
theorem mon_eval (c : R) (n : ℕ) (Y : ℂ) : c * (algebraMap ℂ R Y) ^ n = Y ^ n • c := by
  rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha⟩`. Use `⟨monomial n c + ∑ i ∈ range n, monomial i (a i), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `natDegree_add_le_of_degree_le (natDegree_monomial_le _) (natDegree_sum_le_of_forall_le _ _ fun i hi => (natDegree_monomial_le _).trans (mem_range.1 hi).le)`. Rewrite using `[coeff_add, coeff_monomial, if_pos rfl, finsetSum_coeff, sum_eq_zero, add_zero]`.

Introduce `i hi`. Rewrite using `[coeff_monomial, if_neg (mem_range.1 hi).ne]`. Introduce `Y`. Rewrite using `[ha, eval_add, eval_monomial, eval_finsetSum, mon_eval]`. Use `congr 1`.

Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eval_monomial, mon_eval]`. Introduce and unpack `⟨p, hp, rfl, hf⟩`. Use `⟨p.coeff, fun Y => ?_⟩` and prove the remaining obligations. Rewrite using `[hf, eval_eq_sum_range' (Nat.lt_succ_of_le hp), sum_range_succ, add_comm, mon_eval]`.

Use `congr 1`. Conclude with `sum_congr rfl fun i _ => mon_eval _ _ _`.
-/
theorem lead_iff (n : ℕ) (c : R) (f : ℂ → R) : Lead n c f ↔
    ∃ p : R[X], p.natDegree ≤ n ∧ p.coeff n = c ∧ ∀ Y, f Y = p.eval (algebraMap ℂ R Y) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨monomial n c + ∑ i ∈ range n, monomial i (a i), ?_, ?_, ?_⟩
    · exact natDegree_add_le_of_degree_le (natDegree_monomial_le _)
        (natDegree_sum_le_of_forall_le _ _ fun i hi =>
          (natDegree_monomial_le _).trans (mem_range.1 hi).le)
    · rw [coeff_add, coeff_monomial, if_pos rfl, finsetSum_coeff, sum_eq_zero, add_zero]
      intro i hi
      rw [coeff_monomial, if_neg (mem_range.1 hi).ne]
    · intro Y
      rw [ha, eval_add, eval_monomial, eval_finsetSum, mon_eval]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [eval_monomial, mon_eval]
  · rintro ⟨p, hp, rfl, hf⟩
    refine ⟨p.coeff, fun Y => ?_⟩
    rw [hf, eval_eq_sum_range' (Nat.lt_succ_of_le hp), sum_range_succ, add_comm, mon_eval]
    congr 1
    exact sum_congr rfl fun i _ => mon_eval _ _ _

variable {n m : ℕ} {c d : R} {f g : ℂ → R}

/- English proof (translation)
Rewrite `*` using `[lead_iff]`. Take `⟨p, hp, rfl, hpf⟩` from `hf`. Take `⟨q, hq, rfl, hqg⟩` from `hg`. Use `⟨p * q, natDegree_mul_le_of_le hp hq, coeff_mul_add_eq_of_natDegree_le hp hq, fun Y => ?_⟩` and prove the remaining obligations. Rewrite using `[hpf, hqg]`.

Conclude with `(eval₂_mul_noncomm (RingHom.id R) _ fun k => (Algebra.commutes Y (q.coeff k)).symm).symm`.
-/
theorem Lead.mul (hf : Lead n c f) (hg : Lead m d g) : Lead (n + m) (c * d) fun Y => f Y * g Y := by
  rw [lead_iff] at *
  obtain ⟨p, hp, rfl, hpf⟩ := hf
  obtain ⟨q, hq, rfl, hqg⟩ := hg
  refine ⟨p * q, natDegree_mul_le_of_le hp hq, coeff_mul_add_eq_of_natDegree_le hp hq, fun Y => ?_⟩
  rw [hpf, hqg]
  exact (eval₂_mul_noncomm (RingHom.id R) _ fun k => (Algebra.commutes Y (q.coeff k)).symm).symm

/- English proof (translation)
Take `⟨a, ha⟩` from `hf`. Take `⟨b, hb⟩` from `hg`. Use `⟨fun i => a i + b i, fun Y => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[ha, hb]`.

Simplify using `only [smul_add, sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem Lead.add (hf : Lead n c f) (hg : Lead n d g) : Lead n (c + d) fun Y => f Y + g Y := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun i => a i + b i, fun Y => ?_⟩
  beta_reduce
  rw [ha, hb]
  simp only [smul_add, sum_add_distrib]
  abel

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun Y => by simp⟩`.
-/
theorem Lead.const (c : R) : Lead 0 c fun _ => c := ⟨0, fun Y => by simp⟩

/- English proof (translation)
Take `⟨a, ha⟩` from `hf`. Use `⟨fun i => if i = n then c else a i, fun Y => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[ha, sum_range_succ, if_pos rfl, smul_zero, zero_add, add_comm]`. Use `congr 1`.

Conclude with `sum_congr rfl fun i hi => by rw [if_neg (mem_range.1 hi).ne]`.
-/
theorem Lead.succ (hf : Lead n c f) : Lead (n + 1) 0 f := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨fun i => if i = n then c else a i, fun Y => ?_⟩
  beta_reduce
  rw [ha, sum_range_succ, if_pos rfl, smul_zero, zero_add, add_comm]
  congr 1
  exact sum_congr rfl fun i hi => by rw [if_neg (mem_range.1 hi).ne]

/- English proof (translation)
Proceed by induction on `m, h using Nat.le_induction with`. Consider the case `base => exact hf.succ`. Consider the case `succ k _ ih => exact ih.succ`.
-/
theorem Lead.lt (hf : Lead n c f) (h : n < m) : Lead m 0 f := by
  induction m, h using Nat.le_induction with
  | base => exact hf.succ
  | succ k _ ih => exact ih.succ

/- English proof (translation)
Substitute `hn hc` using the available equality. Take `⟨a, ha⟩` from `hf`. Conclude with `⟨a, fun Y => by rw [hg, ha]⟩`.
-/
theorem Lead.congr (hf : Lead n c f) (hn : n = m) (hc : c = d) (hg : ∀ Y, g Y = f Y) : Lead m d g := by
  subst hn hc
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, fun Y => by rw [hg, ha]⟩

/- English proof (translation)
The claim follows from `((Lead.const a).mul hf).congr (zero_add n) rfl fun _ => rfl`.
-/
theorem Lead.const_mul (a : R) (hf : Lead n c f) : Lead n (a * c) fun Y => a * f Y :=
  ((Lead.const a).mul hf).congr (zero_add n) rfl fun _ => rfl

/- English proof (translation)
The claim follows from `(hf.mul (Lead.const a)).congr (add_zero n) rfl fun _ => rfl`.
-/
theorem Lead.mul_const (a : R) (hf : Lead n c f) : Lead n (c * a) fun Y => f Y * a :=
  (hf.mul (Lead.const a)).congr (add_zero n) rfl fun _ => rfl

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨0, fun Y => by simp⟩`. Consider the case `insert a s ha ih`. Conclude with `((h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))).congr rfl (add_zero 0) fun Y => sum_insert ha`.
-/
theorem Lead.sum {ι : Type} (s : Finset ι) (F : ι → ℂ → R) (h : ∀ i ∈ s, Lead n 0 (F i)) :
    Lead n 0 fun Y => ∑ i ∈ s, F i Y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun Y => by simp⟩
  | insert a s ha ih =>
    exact ((h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))).congr rfl
      (add_zero 0) fun Y => sum_insert ha

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => a, fun Y => by simp [add_comm]⟩`.
-/
theorem Lead.lin (a b : R) : Lead 1 b fun Y => a + Y • b :=
  ⟨fun _ => a, fun Y => by simp [add_comm]⟩

end lead

/- English proof (translation)
Use `⟨fun i => kap P D fun π => (p π).coeff i, fun Y => ?_⟩` and prove the remaining obligations. Establish `h : (fun π => (p π).eval Y) = Y ^ n • c + ∑ i ∈ range n, Y ^ i • fun π => (p π).coeff i`. Use function extensionality and compare the values at `π`. Rewrite using `[eval_eq_sum_range' (Nat.lt_succ_of_le (hp π)), sum_range_succ, hc, add_comm]`. Simplify using `[mul_comm]`.

Use `beta_reduce`. Rewrite using `[h, map_add, map_smul, map_sum]`. Simplify using `only [map_smul]`.
-/
theorem lead_kap (n : ℕ) (p : Ty P → ℂ[X]) (c : Ty P → ℂ) (hp : ∀ π, (p π).natDegree ≤ n)
    (hc : ∀ π, (p π).coeff n = c π) : Lead n (kap P D c) fun Y => kap P D fun π => (p π).eval Y := by
  refine ⟨fun i => kap P D fun π => (p π).coeff i, fun Y => ?_⟩
  have h : (fun π => (p π).eval Y) = Y ^ n • c + ∑ i ∈ range n, Y ^ i • fun π => (p π).coeff i := by
    funext π
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (hp π)), sum_range_succ, hc, add_comm]
    simp [mul_comm]
  beta_reduce
  rw [h, map_add, map_smul, map_sum]
  simp only [map_smul]

/- English proof (translation)
Establish `hm : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).Monic` using `fun π => monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _`. Establish `hd : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).natDegree = s.card` using `fun π => by`. Rewrite using `[natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]`. Simplify using the standard rewrite rules. Use `(lead_kap P D s.card (fun π => ∏ i ∈ s, (X + C (rho P π i : ℂ))) (fun _ => 1) (fun π => (hd π).le) (fun π => ?_)).congr rfl (map_one (kap P D)) fun Y => ?_` and prove the remaining obligations.

Use `(hm π).coeff_natDegree` as an intermediate fact. Rewrite `this` using `[hd π]`. Then use the resulting hypothesis. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `[eval_prod]`.
-/
theorem lead_prod (s : Finset ℕ) :
    Lead s.card (1 : A P D) fun Y => kap P D fun π => ∏ i ∈ s, (Y + (rho P π i : ℂ)) := by
  have hm : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).Monic := fun π =>
    monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _
  have hd : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).natDegree = s.card := fun π => by
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]; simp
  refine (lead_kap P D s.card (fun π => ∏ i ∈ s, (X + C (rho P π i : ℂ))) (fun _ => 1)
    (fun π => (hd π).le) (fun π => ?_)).congr rfl (map_one (kap P D)) fun Y => ?_
  · have := (hm π).coeff_natDegree
    rwa [hd π] at this
  · congr 1; funext π
    simp [eval_prod]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem card_I : (Icc 1 (P.k - 1)).card = P.k - 1 := by simp

/- English proof (translation)
The claim follows from `(lead_prod P D (Icc 1 (P.k - 1))).congr (card_I P) rfl fun _ => rfl`.
-/
theorem lead_xA : Lead (P.k - 1) (1 : A P D) (xA P D) :=
  (lead_prod P D (Icc 1 (P.k - 1))).congr (card_I P) rfl fun _ => rfl

/- English proof (translation)
The claim follows from `((lead_prod P D (Icc 1 (P.k - 1) \ ex)).lt (lt_of_le_of_lt ((card_le_card sdiff_subset).trans (card_I P).le) hm)).congr rfl rfl fun _ => rfl`.
-/
theorem lead_xEx (ex : Finset ℕ) (m : ℕ) (hm : P.k - 1 < m) :
    Lead m (0 : A P D) fun Y => kap P D fun π => xEx P ex π Y :=
  ((lead_prod P D (Icc 1 (P.k - 1) \ ex)).lt
    (lt_of_le_of_lt ((card_le_card sdiff_subset).trans (card_I P).le) hm)).congr rfl rfl fun _ => rfl

/- English proof (translation)
The claim follows from `(Lead.sum _ _ fun l _ => ((lead_xEx P D {l} m hm).const_mul (SS P D l)).congr rfl (mul_zero _) fun _ => rfl).congr rfl rfl fun _ => rfl`.
-/
theorem leading_coeff_S21 (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P D) (weightedSumBis P D) :=
  (Lead.sum _ _ fun l _ => ((lead_xEx P D {l} m hm).const_mul (SS P D l)).congr rfl (mul_zero _)
    fun _ => rfl).congr rfl rfl fun _ => rfl

/- English proof (translation)
The claim follows from `(Lead.sum _ _ fun l _ => ((lead_xEx P D {l} m hm).mul_const (star (SS P D l))).congr rfl (zero_mul _) fun _ => rfl).congr rfl rfl fun _ => rfl`.
-/
theorem leading_term_upper_sum (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P D) (S12 P D) :=
  (Lead.sum _ _ fun l _ => ((lead_xEx P D {l} m hm).mul_const (star (SS P D l))).congr rfl (zero_mul _)
    fun _ => rfl).congr rfl rfl fun _ => rfl

/- English proof (translation)
The claim follows from `(Lead.sum _ _ fun l _ => Lead.sum _ _ fun j _ => ((lead_xEx P D {l, j} m hm).const_mul (star (SS P D l) * SS P D j)).congr rfl (mul_zero _) fun _ => rfl).congr rfl rfl fun _ => rfl`.
-/
theorem leading_coeff_S4 (m : ℕ) (hm : P.k - 1 < m) : Lead m (0 : A P D) (S4 P D) :=
  (Lead.sum _ _ fun l _ => Lead.sum _ _ fun j _ =>
    ((lead_xEx P D {l, j} m hm).const_mul (star (SS P D l) * SS P D j)).congr rfl (mul_zero _)
    fun _ => rfl).congr rfl rfl fun _ => rfl

/- English proof (translation)
The claim follows from `(Lead.lin (-nabA P D - (1 / 2 : ℂ) • (zbA P D * ggiA P D)) (-(zbA P D * ggiA P D))).congr rfl rfl fun Y => by rw [l0_eq_neg_nabla_sub, add_smul, smul_neg]; abel`.
-/
theorem leading_coeff_l0 : Lead 1 (-(zbA P D * ggiA P D)) (l0A P D) :=
  (Lead.lin (-nabA P D - (1 / 2 : ℂ) • (zbA P D * ggiA P D)) (-(zbA P D * ggiA P D))).congr rfl rfl fun Y => by
    rw [l0_eq_neg_nabla_sub, add_smul, smul_neg]; abel

/- English proof (translation)
The claim follows from `(Lead.lin (-nabsA P D + (1 / 2 : ℂ) • (zA P D * ggiA P D)) (-(zA P D * ggiA P D))).congr rfl rfl fun Y => by rw [raising_constant_eq_nabla_star, sub_smul, smul_neg]; abel`.
-/
theorem leading_term_lowering_constant : Lead 1 (-(zA P D * ggiA P D)) (m0A P D) :=
  (Lead.lin (-nabsA P D + (1 / 2 : ℂ) • (zA P D * ggiA P D)) (-(zA P D * ggiA P D))).congr rfl rfl fun Y => by
    rw [raising_constant_eq_nabla_star, sub_smul, smul_neg]; abel

/- English proof (translation)
Unfold `coordinatePolynomial`. Rewrite using `[natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]`. Simplify using `only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]`. Conclude with `card_I P`.
-/
theorem natDegree_x_polynomial (π : Ty P) : (coordinatePolynomial P π).natDegree = P.k - 1 := by
  unfold coordinatePolynomial
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
  simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
  exact card_I P

/- English proof (translation)
Establish `hm : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).Monic` using `monic_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)`. Establish `hd : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).natDegree = 2 * P.k`. Rewrite using `[natDegree_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)]`. Establish `: ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2` using `fun i _ => by`. Rewrite using `[(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]`.

Rewrite using `[sum_congr rfl this]`. Simplify using `[mul_comm]`. Establish `he : ∀ (l : ℕ) (ρ : ℕ → ℂ), (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (ρ j))).natDegree ≤ P.k - 1`. Introduce `l ρ`. Rewrite using `[natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]`.

Simplify using `only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]`. Conclude with `(card_le_card (erase_subset _ _)).trans (card_I P).le`. Establish `ht : (∑ l ∈ Icc 1 (P.k - 1), C ((Nrm P l π : ℝ) : ℂ) * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (rho P π j : ℂ))) * ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((rho P π j : ℂ) + 1)))).natDegree ≤ (P.k - 1) + (P.k - 1)` using `natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_le _ _).trans (natDegree_mul_le_of_le (he l _) (he l _))`. Establish `hq : (qP P).natDegree ≤ 2 * P.k` using `(natDegree_C_mul_le _ _).trans hd.le`. Prove the components needed by the constructor for the conclusion.

Conclude with `natDegree_add_le_of_degree_le hq (ht.trans (by omega))`. Unfold `wNum`. Rewrite using `[coeff_add, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ht (by omega)), add_zero, qP, coeff_C_mul, ← hd, hm.coeff_natDegree, mul_one]`.
-/
theorem wNum_deg (hk : 1 ≤ P.k) (π : Ty P) : (wNum P π).natDegree ≤ 2 * P.k ∧
    (wNum P π).coeff (2 * P.k) = -((P.T : ℂ) * P.T') := by
  have hm : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)
  have hd : (∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))).natDegree
      = 2 * P.k := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _)]
    have : ∀ i ∈ Icc 1 P.k,
        ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := fun i _ => by
      rw [(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
    rw [sum_congr rfl this]
    simp [mul_comm]
  have he : ∀ (l : ℕ) (ρ : ℕ → ℂ), (∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (ρ j))).natDegree ≤ P.k - 1 := by
    intro l ρ
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_add_C _]
    simp only [natDegree_X_add_C, sum_const, smul_eq_mul, mul_one]
    exact (card_le_card (erase_subset _ _)).trans (card_I P).le
  have ht : (∑ l ∈ Icc 1 (P.k - 1), C ((Nrm P l π : ℝ) : ℂ) *
      ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C (rho P π j : ℂ))) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (X + C ((rho P π j : ℂ) + 1)))).natDegree ≤
      (P.k - 1) + (P.k - 1) :=
    natDegree_sum_le_of_forall_le _ _ fun l _ => (natDegree_C_mul_le _ _).trans
      (natDegree_mul_le_of_le (he l _) (he l _))
  have hq : (qP P).natDegree ≤ 2 * P.k := (natDegree_C_mul_le _ _).trans hd.le
  constructor
  · exact natDegree_add_le_of_degree_le hq (ht.trans (by omega))
  · unfold wNum
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ht (by omega)), add_zero, qP,
      coeff_C_mul, ← hd, hm.coeff_natDegree, mul_one]

/- English proof (translation)
Establish `hk` using `hP.k_pos`. Establish `hm` using `coordinate_polynomial_monic P π`. Establish `hd` using `natDegree_x_polynomial P π`. Take `⟨h1, h2⟩` from `wNum_deg P hk π`. Establish `h3 : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1`.

Rewrite using `[natDegree_divByMonic _ hm, hd]`. Use linear arithmetic over natural numbers and integers. Use `⟨h3, ?_⟩` and prove the remaining obligations. Establish `h6` using `coeff_mul_add_eq_of_natDegree_le hd.le h3`. Rewrite `h6` using `[← weight_exact P hP π]`.

Establish `h7 : (coordinatePolynomial P π).coeff (P.k - 1) = 1`. Use `hm.coeff_natDegree` as an intermediate fact. Rewrite `this` using `[hd]`. Then use the resulting hypothesis. Establish `e : P.k - 1 + (P.k + 1) = 2 * P.k` using `by omega`. Rewrite `h6` using `[h7, one_mul, e, h2]`.

Conclude with `h6.symm`.
-/
theorem wq_deg (hP : P.OK) (π : Ty P) : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1 ∧
    (wNum P π /ₘ coordinatePolynomial P π).coeff (P.k + 1) = -((P.T : ℂ) * P.T') := by
  have hk := hP.k_pos
  have hm := coordinate_polynomial_monic P π
  have hd := natDegree_x_polynomial P π
  obtain ⟨h1, h2⟩ := wNum_deg P hk π
  have h3 : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1 := by
    rw [natDegree_divByMonic _ hm, hd]; omega
  refine ⟨h3, ?_⟩
  have h6 := coeff_mul_add_eq_of_natDegree_le hd.le h3
  rw [← weight_exact P hP π] at h6
  have h7 : (coordinatePolynomial P π).coeff (P.k - 1) = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e : P.k - 1 + (P.k + 1) = 2 * P.k := by omega
  rw [h7, one_mul, e, h2] at h6
  exact h6.symm

/- English proof (translation)
The claim follows from `(fn_comm P D _ _ _ _).eq`.
-/
theorem gg_zb : ggA P D * zbA P D = zbA P D * ggA P D := (fn_comm P D _ _ _ _).eq
/- English proof (translation)
The claim follows from `(fn_comm P D _ _ _ _).eq`.
-/
theorem GG_commute_z : ggA P D * zA P D = zA P D * ggA P D := (fn_comm P D _ _ _ _).eq

/- English proof (translation)
Rewrite using `[← mul_assoc, gg_zb, mul_assoc, gg_ggi, mul_one]`.
-/
theorem gg_zb_ggi : ggA P D * (zbA P D * ggiA P D) = zbA P D := by
  rw [← mul_assoc, gg_zb, mul_assoc, gg_ggi, mul_one]

/- English proof (translation)
Rewrite using `[← mul_assoc, GG_commute_z, mul_assoc, gg_ggi, mul_one]`.
-/
theorem gg_z_ggi : ggA P D * (zA P D * ggiA P D) = zA P D := by
  rw [← mul_assoc, GG_commute_z, mul_assoc, gg_ggi, mul_one]

/- English proof (translation)
The claim follows from `((lead_xA P D).const_mul (ggA P D)).congr rfl (mul_one _) fun _ => rfl`.
-/
theorem leading_coeff_t22 : Lead (P.k - 1) (ggA P D) (t22 P D) :=
  ((lead_xA P D).const_mul (ggA P D)).congr rfl (mul_one _) fun _ => rfl

/- English proof (translation)
The claim follows from `((((lead_xA P D).const_mul (ggA P D)).mul (leading_coeff_l0 P D)).congr (m := P.k) (by omega) rfl (fun _ => rfl) |>.add (leading_coeff_S21 P D P.k (by omega))).congr rfl (by rw [mul_one, mul_neg, gg_zb_ggi, add_zero]) fun _ => rfl`.
-/
theorem leading_term_lower_left (hk : 1 ≤ P.k) : Lead P.k (-zbA P D) (t21 P D) :=
  ((((lead_xA P D).const_mul (ggA P D)).mul (leading_coeff_l0 P D)).congr (m := P.k) (by omega) rfl (fun _ => rfl)
    |>.add (leading_coeff_S21 P D P.k (by omega))).congr rfl
    (by rw [mul_one, mul_neg, gg_zb_ggi, add_zero]) fun _ => rfl

/- English proof (translation)
The claim follows from `((((lead_xA P D).const_mul (ggA P D)).mul (leading_term_lowering_constant P D)).congr (m := P.k) (by omega) rfl (fun _ => rfl) |>.add (leading_term_upper_sum P D P.k (by omega))).congr rfl (by rw [mul_one, mul_neg, gg_z_ggi, add_zero]) fun _ => rfl`.
-/
theorem leading_coeff_t12 (hk : 1 ≤ P.k) : Lead P.k (-zA P D) (t12 P D) :=
  ((((lead_xA P D).const_mul (ggA P D)).mul (leading_term_lowering_constant P D)).congr (m := P.k) (by omega) rfl (fun _ => rfl)
    |>.add (leading_term_upper_sum P D P.k (by omega))).congr rfl
    (by rw [mul_one, mul_neg, gg_z_ggi, add_zero]) fun _ => rfl

/- English proof (translation)
Establish `e : ggA P D * 1 * -(zA P D * ggiA P D) * -(zbA P D * ggiA P D) = zA P D * zbA P D * ggiA P D`. Rewrite using `[mul_one, mul_neg (ggA P D), gg_z_ggi, neg_mul_neg, mul_assoc]`. Rewrite using `[e, kap_const, ← Algebra.commutes, ← add_mul]`. Establish `h : algebraMap ℂ (A P D) (-((P.T : ℂ) * P.T')) + zA P D * zbA P D = ggA P D`. Rewrite using `[gg_def, map_neg, Par.TT]`.

Use `push_cast`. Normalize the expressions using the abelian group laws. Rewrite using `[h, gg_ggi]`.
-/
theorem lead_coef : ggiA P D * (kap P D fun _ => -((P.T : ℂ) * P.T')) +
    ggA P D * 1 * -(zA P D * ggiA P D) * -(zbA P D * ggiA P D) = 1 := by
  have e : ggA P D * 1 * -(zA P D * ggiA P D) * -(zbA P D * ggiA P D) = zA P D * zbA P D * ggiA P D := by
    rw [mul_one, mul_neg (ggA P D), gg_z_ggi, neg_mul_neg, mul_assoc]
  rw [e, kap_const, ← Algebra.commutes, ← add_mul]
  have h : algebraMap ℂ (A P D) (-((P.T : ℂ) * P.T')) + zA P D * zbA P D = ggA P D := by
    rw [gg_def, map_neg, Par.TT]; push_cast; abel
  rw [h, gg_ggi]

/- English proof (translation)
Establish `hk` using `hP.k_pos`. Establish `h1 : Lead (P.k + 1) (ggiA P D * (kap P D fun _ => -((P.T : ℂ) * P.T'))) fun Y => ggiA P D * (kap P D fun π => wC P π Y)` using `(lead_kap P D (P.k + 1) (fun π => wNum P π /ₘ coordinatePolynomial P π) _ (fun π => (wq_deg P hP π).1) (fun π => (wq_deg P hP π).2)).const_mul (ggiA P D)`. Establish `h2 : Lead (P.k + 1) (ggA P D * 1 * -(zA P D * ggiA P D) * -(zbA P D * ggiA P D)) fun Y => ggA P D * xA P D Y * m0A P D Y * l0A P D Y` using `((((lead_xA P D).const_mul (ggA P D)).mul (leading_term_lowering_constant P D)).mul (leading_coeff_l0 P D)).congr (by omega) rfl fun _ => rfl`. Establish `h3 : Lead (P.k + 1) (0 : A P D) fun Y => ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y` using `((((leading_term_lowering_constant P D).const_mul (ggA P D)).mul_const (ggiA P D)).mul (leading_coeff_S21 P D P.k (by omega))).congr (by omega) (mul_zero _) fun _ => rfl`. Establish `h4 : Lead (P.k + 1) (0 : A P D) fun Y => S12 P D Y * l0A P D Y` using `((leading_term_upper_sum P D P.k (by omega)).mul (leading_coeff_l0 P D)).congr rfl (zero_mul _) fun _ => rfl`.

Establish `h5 : Lead (P.k + 1) (0 : A P D) fun Y => ggiA P D * S4 P D Y` using `((leading_coeff_S4 P D (P.k + 1) (by omega)).const_mul (ggiA P D)).congr rfl (mul_zero _) fun _ => rfl`. Conclude with `((((h1.add h2).add h3).add h4).add h5).congr rfl (by rw [lead_coef, add_zero, add_zero, add_zero]) fun _ => rfl`.
-/
theorem leading_coeff_t11 (hP : P.OK) : Lead (P.k + 1) (1 : A P D) (t11 P D) := by
  have hk := hP.k_pos
  have h1 : Lead (P.k + 1) (ggiA P D * (kap P D fun _ => -((P.T : ℂ) * P.T')))
      fun Y => ggiA P D * (kap P D fun π => wC P π Y) :=
    (lead_kap P D (P.k + 1) (fun π => wNum P π /ₘ coordinatePolynomial P π) _ (fun π => (wq_deg P hP π).1)
      (fun π => (wq_deg P hP π).2)).const_mul (ggiA P D)
  have h2 : Lead (P.k + 1) (ggA P D * 1 * -(zA P D * ggiA P D) * -(zbA P D * ggiA P D))
      fun Y => ggA P D * xA P D Y * m0A P D Y * l0A P D Y :=
    ((((lead_xA P D).const_mul (ggA P D)).mul (leading_term_lowering_constant P D)).mul (leading_coeff_l0 P D)).congr (by omega) rfl fun _ => rfl
  have h3 : Lead (P.k + 1) (0 : A P D) fun Y => ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y :=
    ((((leading_term_lowering_constant P D).const_mul (ggA P D)).mul_const (ggiA P D)).mul (leading_coeff_S21 P D P.k (by omega))).congr
      (by omega) (mul_zero _) fun _ => rfl
  have h4 : Lead (P.k + 1) (0 : A P D) fun Y => S12 P D Y * l0A P D Y :=
    ((leading_term_upper_sum P D P.k (by omega)).mul (leading_coeff_l0 P D)).congr rfl (zero_mul _) fun _ => rfl
  have h5 : Lead (P.k + 1) (0 : A P D) fun Y => ggiA P D * S4 P D Y :=
    ((leading_coeff_S4 P D (P.k + 1) (by omega)).const_mul (ggiA P D)).congr rfl (mul_zero _) fun _ => rfl
  exact ((((h1.add h2).add h3).add h4).add h5).congr rfl
    (by rw [lead_coef, add_zero, add_zero, add_zero]) fun _ => rfl

/- English proof (translation)
Introduce `P D _ hP`. Establish `hk` using `hP.k_pos`. Take `⟨a11, h11⟩` from `leading_coeff_t11 P D hP`. Take `⟨a12, h12⟩` from `leading_coeff_t12 P D hk`. Take `⟨a21, h21⟩` from `leading_term_lower_left P D hk`.

Take `⟨a22, h22⟩` from `leading_coeff_t22 P D`. Conclude with `⟨a11, a12, a21, a22, fun Y => ⟨h11 Y, by rw [h12 Y, smul_neg], by rw [h21 Y, smul_neg], h22 Y⟩⟩`.
-/
theorem qQLeading : QQLeading := by
  intro P D _ hP
  have hk := hP.k_pos
  obtain ⟨a11, h11⟩ := leading_coeff_t11 P D hP
  obtain ⟨a12, h12⟩ := leading_coeff_t12 P D hk
  obtain ⟨a21, h21⟩ := leading_term_lower_left P D hk
  obtain ⟨a22, h22⟩ := leading_coeff_t22 P D
  exact ⟨a11, a12, a21, a22, fun Y => ⟨h11 Y, by rw [h12 Y, smul_neg], by rw [h21 Y, smul_neg], h22 Y⟩⟩

/- English proof (translation)
Unfold `xC xEx`. Rewrite using `[sdiff_singleton_eq_erase]`. Conclude with `(mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) hj).symm`.
-/
theorem xC_split (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) (Y : ℂ) :
    xC P π Y = (Y + (rho P π j : ℂ)) * xEx P {j} π Y := by
  unfold xC xEx
  rw [sdiff_singleton_eq_erase]
  exact (mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) hj).symm

/- English proof (translation)
Unfold `xEx`. Rewrite using `[sdiff_insert]`. Conclude with `(mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) ha).symm`.
-/
theorem xEx_insert (ex : Finset ℕ) (a : ℕ) (ha : a ∈ Icc 1 (P.k - 1) \ ex) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (Y + (rho P π a : ℂ)) * xEx P (insert a ex) π Y := by
  unfold xEx
  rw [sdiff_insert]
  exact (mul_prod_erase _ (fun i => Y + (rho P π i : ℂ)) ha).symm

/- English proof (translation)
Unfold `xC at hx`. Conclude with `Finset.prod_ne_zero_iff.1 hx j hj`.
-/
theorem fac_ne {π : Ty P} {Y : ℂ} (hx : xC P π Y ≠ 0) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    Y + (rho P π j : ℂ) ≠ 0 := by
  unfold xC at hx
  exact Finset.prod_ne_zero_iff.1 hx j hj

/- English proof (translation)
Rewrite using `[xA, ← kap_mul]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Rewrite using `[xC_split P j hj, mul_comm (Y + (rho P π j : ℂ)), mul_assoc, mul_inv_cancel₀ (fac_ne P (hx π) hj), mul_one]`.
-/
theorem x_iv (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) :
    xA P D Y * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P D fun π => xEx P {j} π Y := by
  rw [xA, ← kap_mul]
  congr 1; funext π
  rw [xC_split P j hj, mul_comm (Y + (rho P π j : ℂ)), mul_assoc, mul_inv_cancel₀ (fac_ne P (hx π) hj),
    mul_one]

/- English proof (translation)
Unfold `weightedSumBis`. Rewrite using `[mul_sum]`. Use `sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, x_iv P D Y hx j hj]`. Conclude with `(kap_ss P D j _ (xEx_up P j _ (by simp) _)).eq`.
-/
theorem x_sl (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    xA P D Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j = weightedSumBis P D Y := by
  unfold weightedSumBis
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, x_iv P D Y hx j hj]
  exact (kap_ss P D j _ (xEx_up P j _ (by simp) _)).eq

/- English proof (translation)
Unfold `S12`. Rewrite using `[mul_sum]`. Use `sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, x_iv P D Y hx j hj]`.
-/
theorem x_sm (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    xA P D Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D j) =
      S12 P D Y := by
  unfold S12
  rw [mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, x_iv P D Y hx j hj]

/- English proof (translation)
Rewrite using `[mul_assoc, ← mul_assoc (kap P D f), kap_ggi, mul_assoc, ← mul_assoc, gg_ggi, one_mul]`.
-/
theorem gxg (f : Ty P → ℂ) (Z : A P D) : ggA P D * kap P D f * (ggiA P D * Z) = kap P D f * Z := by
  rw [mul_assoc, ← mul_assoc (kap P D f), kap_ggi, mul_assoc, ← mul_assoc, gg_ggi, one_mul]

/- English proof (translation)
The claim follows from `gxg P D _ Z`.
-/
theorem gxg' (Y : ℂ) (Z : A P D) : ggA P D * xA P D Y * (ggiA P D * Z) = xA P D Y * Z := gxg P D _ Z

/- English proof (translation)
Rewrite using `[t21, t22, lA, mul_add, gxg', x_sl P D Y hx]`.
-/
theorem lower_left_normal_form (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) : t21 P D Y = t22 P D Y * lA P D Y := by
  rw [t21, t22, lA, mul_add, gxg', x_sl P D Y hx]

/- English proof (translation)
Rewrite using `[t12, t22, mA, mul_add, gxg', x_sm P D Y hx]`.
-/
theorem upper_right_normal_form (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) : t12 P D Y = t22 P D Y * mA P D Y := by
  rw [t12, t22, mA, mul_add, gxg', x_sm P D Y hx]

/- English proof (translation)
Unfold `coordinatePolynomial xC`. Rewrite using `[eval_prod]`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eval_add, eval_X, eval_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_x_polynomial (π : Ty P) (Y : ℂ) : (coordinatePolynomial P π).eval Y = xC P π (Y + 1) := by
  unfold coordinatePolynomial xC
  rw [eval_prod]
  refine prod_congr rfl fun i _ => ?_
  rw [eval_add, eval_X, eval_C]; ring

/- English proof (translation)
Unfold `qP qC`. Rewrite using `[eval_mul, eval_C, eval_prod]`. Use `congr 1`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[eval_mul, eval_add, eval_add, eval_X, eval_C, eval_C]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_qP (Y : ℂ) : (qP P).eval Y = qC P Y := by
  unfold qP qC
  rw [eval_mul, eval_C, eval_prod]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  rw [eval_mul, eval_add, eval_add, eval_X, eval_C, eval_C]; ring

/- English proof (translation)
Unfold `wNum`. Rewrite using `[eval_add, eval_qP, eval_finsetSum]`. Use `congr 1`. Use `sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[eval_mul, eval_C, eval_mul, eval_prod, eval_prod]`.

Unfold `xEx`. Rewrite using `[sdiff_singleton_eq_erase]`. Use `congr 2`. Conclude with `prod_congr rfl fun i _ => by rw [eval_add, eval_X, eval_C]`. Conclude with `prod_congr rfl fun i _ => by rw [eval_add, eval_X, eval_C]; ring`.
-/
theorem eval_wNum (π : Ty P) (Y : ℂ) : (wNum P π).eval Y = qC P Y +
    ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1)) := by
  unfold wNum
  rw [eval_add, eval_qP, eval_finsetSum]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [eval_mul, eval_C, eval_mul, eval_prod, eval_prod]
  unfold xEx
  rw [sdiff_singleton_eq_erase]
  congr 2
  · exact prod_congr rfl fun i _ => by rw [eval_add, eval_X, eval_C]
  · exact prod_congr rfl fun i _ => by rw [eval_add, eval_X, eval_C]; ring

/- English proof (translation)
Establish `hW : (wNum P π).eval Y = xC P π (Y + 1) * wC P π Y`. Establish `h` using `congrArg (eval Y) (weight_exact P hP π)`. Rewrite `h` using `[eval_mul, eval_x_polynomial]`. Conclude with `h`. Apply `mul_left_cancel₀ h1` to reduce the goal to its premises.

Rewrite using `[← hW, eval_wNum, mul_add, mul_sum]`. Use `congr 1`. Rewrite using `[mul_comm (qC P Y), ← mul_assoc, mul_inv_cancel₀ h1, one_mul]`. Use `sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `hne : Y + 1 + (rho P π l : ℂ) ≠ 0` using `fac_ne P h1 hl`.

Establish `e : Y + (rho P π l : ℂ) + 1 = Y + 1 + (rho P π l : ℂ)` using `by ring`. Rewrite using `[xC_split P l hl π (Y + 1), e]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_inv_cancel₀ hne, one_mul]`. Use `_ = _ := by ring`.
-/
theorem wC_id (hP : P.OK) (π : Ty P) (Y : ℂ) (h1 : xC P π (Y + 1) ≠ 0) :
    wC P π Y = qC P Y * (xC P π (Y + 1))⁻¹ +
      ∑ l ∈ Icc 1 (P.k - 1), xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
  have hW : (wNum P π).eval Y = xC P π (Y + 1) * wC P π Y := by
    have h := congrArg (eval Y) (weight_exact P hP π)
    rw [eval_mul, eval_x_polynomial] at h
    exact h
  apply mul_left_cancel₀ h1
  rw [← hW, eval_wNum, mul_add, mul_sum]
  congr 1
  · rw [mul_comm (qC P Y), ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  · refine sum_congr rfl fun l hl => ?_
    have hne : Y + 1 + (rho P π l : ℂ) ≠ 0 := fac_ne P h1 hl
    have e : Y + (rho P π l : ℂ) + 1 = Y + 1 + (rho P π l : ℂ) := by ring
    rw [xC_split P l hl π (Y + 1), e]
    calc ((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1))
        = ((Y + 1 + (rho P π l : ℂ)) * (Y + 1 + (rho P π l : ℂ))⁻¹) *
          (((Nrm P l π : ℝ) : ℂ) * (xEx P {l} π Y * xEx P {l} π (Y + 1))) := by
          rw [mul_inv_cancel₀ hne, one_mul]
      _ = _ := by ring

/- English proof (translation)
Rewrite using `[rho_raise P l π π' h l hl, if_pos rfl]`.
-/
theorem rho_up_same {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) {π π' : Ty P} (h : Up P l π π') :
    rho P π' l = rho P π l + 1 := by
  rw [rho_raise P l π π' h l hl, if_pos rfl]

/- English proof (translation)
Rewrite using `[rho_raise P l π π' h j hj, if_neg hjl, add_zero]`.
-/
theorem rho_up_ne {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) {π π' : Ty P} (h : Up P l π π') :
    rho P π' j = rho P π j := by
  rw [rho_raise P l π π' h j hj, if_neg hjl, add_zero]

/- English proof (translation)
Rewrite using `[ss_shift P D l (fun π => (Y + (rho P π l : ℂ) + 1)⁻¹) (fun π => (Y + (rho P π l : ℂ))⁻¹) (fun π π' h => by rw [rho_up_same P hl h]; push_cast; rw [add_assoc]), mul_assoc, ← mul_assoc (star (SS P D l)), hN, ← mul_assoc, ← kap_mul, ← kap_mul]`.
-/
theorem diag_term {l : ℕ} (hN : star (SS P D l) * SS P D l = kap P D fun π => ((Nrm P l π : ℝ) : ℂ)) (Y : ℂ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P D fun π => xEx P {l} π Y) * star (SS P D l) * ((kap P D fun π => (Y + (rho P π l : ℂ))⁻¹) * SS P D l) =
      kap P D fun π => xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
  rw [ss_shift P D l (fun π => (Y + (rho P π l : ℂ) + 1)⁻¹) (fun π => (Y + (rho P π l : ℂ))⁻¹)
    (fun π π' h => by rw [rho_up_same P hl h]; push_cast; rw [add_assoc]),
    mul_assoc, ← mul_assoc (star (SS P D l)), hN, ← mul_assoc, ← kap_mul, ← kap_mul]

/- English proof (translation)
Establish `h1 : star (SS P D l) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) = (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D l)` using `(kap_sss P D l _ fun π π' h => by rw [rho_up_ne P hj hjl h]).eq.symm`. Establish `h2 : (kap P D fun π => xEx P {l} π Y) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P D fun π => xEx P {l, j} π Y`. Rewrite using `[← kap_mul]`. Use `congr 1`. Use function extensionality and compare the values at `π`.

Rewrite using `[xEx_insert P {l} j (by simp [mem_sdiff, hjl]; simpa using hj), Finset.pair_comm j l, mul_comm (Y + (rho P π j : ℂ)), mul_assoc, mul_inv_cancel₀ (fac_ne P (hx π) hj), mul_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (kap P D fun π => xEx P {l} π Y) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * (star (SS P D l) * SS P D j) := by rw [h1]; simp only [mul_assoc]`. Use `_ = _ := by`.

Rewrite using `[h2]`. Conclude with `((kap_sss P D l _ (xEx_up P l _ (by simp) _)).mul_right (kap_ss P D j _ (xEx_up P j _ (by simp) _))).eq`.
-/
theorem off_term (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) {l j : ℕ}
    (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    (kap P D fun π => xEx P {l} π Y) * star (SS P D l) * ((kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j) =
      star (SS P D l) * SS P D j * kap P D fun π => xEx P {l, j} π Y := by
  have h1 : star (SS P D l) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) =
      (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D l) :=
    (kap_sss P D l _ fun π π' h => by rw [rho_up_ne P hj hjl h]).eq.symm
  have h2 : (kap P D fun π => xEx P {l} π Y) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) =
      kap P D fun π => xEx P {l, j} π Y := by
    rw [← kap_mul]
    congr 1; funext π
    rw [xEx_insert P {l} j (by simp [mem_sdiff, hjl]; simpa using hj), Finset.pair_comm j l,
      mul_comm (Y + (rho P π j : ℂ)), mul_assoc, mul_inv_cancel₀ (fac_ne P (hx π) hj), mul_one]
  calc (kap P D fun π => xEx P {l} π Y) * star (SS P D l) * ((kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j)
      = (kap P D fun π => xEx P {l} π Y) * (star (SS P D l) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹)) * SS P D j := by
        simp only [mul_assoc]
    _ = (kap P D fun π => xEx P {l} π Y) * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) *
          (star (SS P D l) * SS P D j) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by
        rw [h2]
        exact ((kap_sss P D l _ (xEx_up P l _ (by simp) _)).mul_right
          (kap_ss P D j _ (xEx_up P j _ (by simp) _))).eq

/- English proof (translation)
Establish `h : ∀ l ∈ Icc 1 (P.k - 1), (kap P D fun π => xEx P {l} π Y) * star (SS P D l) * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j = (kap P D fun π => xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + ∑ j ∈ (Icc 1 (P.k - 1)).erase l, …`. Introduce `l hl`. Rewrite using `[mul_sum, ← add_sum_erase _ _ hl, diag_term P D (hN l hl) Y hl, sum_congr rfl fun j hj => off_term P D Y hx (mem_of_mem_erase hj) (ne_of_mem_erase hj)]`. Rewrite using `[S12, S4, sum_mul, sum_congr rfl h, sum_add_distrib, kap_sum]`.
-/
theorem upper_sum_mul_inverse_sum (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P D l) * SS P D l = kap P D fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    S12 P D Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j =
      (kap P D fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + S4 P D Y := by
  have h : ∀ l ∈ Icc 1 (P.k - 1), (kap P D fun π => xEx P {l} π Y) * star (SS P D l) *
      ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j =
      (kap P D fun π => xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) +
        ∑ j ∈ (Icc 1 (P.k - 1)).erase l, star (SS P D l) * SS P D j * kap P D fun π => xEx P {l, j} π Y := by
    intro l hl
    rw [mul_sum, ← add_sum_erase _ _ hl, diag_term P D (hN l hl) Y hl,
      sum_congr rfl fun j hj => off_term P D Y hx (mem_of_mem_erase hj) (ne_of_mem_erase hj)]
  rw [S12, S4, sum_mul, sum_congr rfl h, sum_add_distrib, kap_sum]

/- English proof (translation)
The claim follows from `(kappa_commute_raising_constant P D _ Y').eq`.
-/
theorem coordinate_commute_raising (Y Y' : ℂ) : xA P D Y * m0A P D Y' = m0A P D Y' * xA P D Y := (kappa_commute_raising_constant P D _ Y').eq
/- English proof (translation)
The claim follows from `kap_ggi P D _`.
-/
theorem xA_ggi (Y : ℂ) : xA P D Y * ggiA P D = ggiA P D * xA P D Y := kap_ggi P D _

/- English proof (translation)
The claim follows from `(upper_sum_commute_scalar P D Y _).eq`.
-/
theorem upper_sum_gamma_inv_comm (Y : ℂ) : S12 P D Y * ggiA P D = ggiA P D * S12 P D Y := (upper_sum_commute_scalar P D Y _).eq

/- English proof (translation)
Rewrite using `[← upper_right_normal_form P D Y hx, t11, t12, lA]`. Use `set Sl := ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j with hSl`. Establish `e1 : ggA P D * xA P D Y * m0A P D Y * (ggiA P D * Sl) = ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y`. Rewrite using `[← x_sl P D Y hx, ← hSl]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [mul_assoc]`. Use `_ = ggA P D * (m0A P D Y * xA P D Y) * (ggiA P D * Sl) := by rw [coordinate_commute_raising]`. Use `_ = ggA P D * m0A P D Y * (xA P D Y * ggiA P D) * Sl := by simp only [mul_assoc]`. Use `_ = ggA P D * m0A P D Y * (ggiA P D * xA P D Y) * Sl := by rw [xA_ggi]`. Use `_ = _ := by simp only [mul_assoc]`.

Establish `e2 : S12 P D Y * (ggiA P D * Sl) = ggiA P D * (S12 P D Y * Sl)`. Rewrite using `[← mul_assoc, upper_sum_gamma_inv_comm, mul_assoc]`. Establish `e4 : (kap P D fun π => wC P π Y) = qC P Y • (kap P D fun π => (xC P π (Y + 1))⁻¹) + kap P D fun π => ∑ l ∈ Icc 1 (P.k - 1), xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹`. Rewrite using `[← kap_smul, ← kap_add]`. Use `congr 1`.

Use function extensionality and compare the values at `π`. Conclude with `wC_id P hP π Y (hx1 π)`. Rewrite using `[add_mul, mul_add, mul_add, e1, e2, upper_sum_mul_inverse_sum P D hN Y hx, e4, mul_add, mul_add, mul_smul_comm]`. Normalize the expressions using the abelian group laws.
-/
theorem upper_left_normal_form (hP : P.OK)
    (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P D l) * SS P D l = kap P D fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) (hx1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    t11 P D Y = qC P Y • (ggiA P D * kap P D fun π => (xC P π (Y + 1))⁻¹) + t22 P D Y * mA P D Y * lA P D Y := by
  rw [← upper_right_normal_form P D Y hx, t11, t12, lA]
  set Sl := ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j with hSl
  have e1 : ggA P D * xA P D Y * m0A P D Y * (ggiA P D * Sl) = ggA P D * m0A P D Y * ggiA P D * weightedSumBis P D Y := by
    rw [← x_sl P D Y hx, ← hSl]
    calc ggA P D * xA P D Y * m0A P D Y * (ggiA P D * Sl) = ggA P D * (xA P D Y * m0A P D Y) * (ggiA P D * Sl) := by
          simp only [mul_assoc]
      _ = ggA P D * (m0A P D Y * xA P D Y) * (ggiA P D * Sl) := by rw [coordinate_commute_raising]
      _ = ggA P D * m0A P D Y * (xA P D Y * ggiA P D) * Sl := by simp only [mul_assoc]
      _ = ggA P D * m0A P D Y * (ggiA P D * xA P D Y) * Sl := by rw [xA_ggi]
      _ = _ := by simp only [mul_assoc]
  have e2 : S12 P D Y * (ggiA P D * Sl) = ggiA P D * (S12 P D Y * Sl) := by
    rw [← mul_assoc, upper_sum_gamma_inv_comm, mul_assoc]
  have e4 : (kap P D fun π => wC P π Y) = qC P Y • (kap P D fun π => (xC P π (Y + 1))⁻¹) +
      kap P D fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹ := by
    rw [← kap_smul, ← kap_add]
    congr 1; funext π
    exact wC_id P hP π Y (hx1 π)
  rw [add_mul, mul_add, mul_add, e1, e2, upper_sum_mul_inverse_sum P D hN Y hx, e4, mul_add, mul_add, mul_smul_comm]
  abel

/- English proof (translation)
The claim follows from `(fn_comm P D _ _ _ _).eq`.
-/
theorem gamma_inv_commute_zeta : ggiA P D * zA P D = zA P D * ggiA P D := (fn_comm P D _ _ _ _).eq

/- English proof (translation)
Rewrite using `[l0_eq_neg_nabla_sub, raising_constant_eq_nabla_star, star_sub, star_neg, star_smul, star_mul, star_nab, star_zb, star_ggi, star_add, star_sub, star_one, star_half, hY, gamma_inv_commute_zeta]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_l0_shift (Y : ℂ) (hY : star Y = Y) : star (l0A P D (Y - 1)) = m0A P D Y := by
  rw [l0_eq_neg_nabla_sub, raising_constant_eq_nabla_star, star_sub, star_neg, star_smul, star_mul, star_nab, star_zb, star_ggi, star_add,
    star_sub, star_one, star_half, hY, gamma_inv_commute_zeta]
  congr 2; ring

/- English proof (translation)
Unfold `mA lA`. Rewrite using `[star_add, star_l0_shift P D Y hY, star_mul, star_ggi, star_sum]`. Use `congr 1`. Establish `h : ∀ j ∈ Icc 1 (P.k - 1), star ((kap P D fun π => (Y - 1 + (rho P π j : ℂ))⁻¹) * SS P D j) = (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D j)`. Introduce `j hj`.

Rewrite using `[star_mul, star_kap]`. Use `sss_shift P D j _ _ fun π π' h => ?_` and prove the remaining obligations. Rewrite using `[rho_up_same P hj h, star_inv₀, star_add, star_sub, star_one, hY, Complex.star_def, Complex.conj_ofReal]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_congr rfl h]`. Conclude with `(Commute.sum_left _ _ _ fun j _ => (kap_sc P D _ _).mul_left (sss_sc P D j _)).eq.symm`.
-/
theorem mA_star (Y : ℂ) (hY : star Y = Y) : mA P D Y = star (lA P D (Y - 1)) := by
  unfold mA lA
  rw [star_add, star_l0_shift P D Y hY, star_mul, star_ggi, star_sum]
  congr 1
  have h : ∀ j ∈ Icc 1 (P.k - 1), star ((kap P D fun π => (Y - 1 + (rho P π j : ℂ))⁻¹) * SS P D j) =
      (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D j) := by
    intro j hj
    rw [star_mul, star_kap]
    refine sss_shift P D j _ _ fun π π' h => ?_
    rw [rho_up_same P hj h, star_inv₀, star_add, star_sub, star_one, hY, Complex.star_def,
      Complex.conj_ofReal]
    congr 1; push_cast; ring
  rw [sum_congr rfl h]
  exact (Commute.sum_left _ _ _ fun j _ => (kap_sc P D _ _).mul_left (sss_sc P D j _)).eq.symm

/- English proof (translation)
Introduce `P D _ hP Y hx`. Conclude with `⟨lower_left_normal_form P D Y hx, upper_right_normal_form P D Y hx, fun hx1 => upper_left_normal_form P D hP (fun l hl => (hN P D hP l hl).1) Y hx hx1, mA_star P D Y⟩`.
-/
theorem qQNormal_of (hN : SSNorm) : QQNormal := by
  intro P D _ hP Y hx
  exact ⟨lower_left_normal_form P D Y hx, upper_right_normal_form P D Y hx,
    fun hx1 => upper_left_normal_form P D hP (fun l hl => (hN P D hP l hl).1) Y hx hx1, mA_star P D Y⟩

end

end Formalism.FourierDecayAlt.P.MAx1.D5

namespace Formalism.FourierDecayAlt.P.MAx1

/- English proof (translation)
The claim follows from `D5.qQNormal_of sSNorm`.
-/
theorem qQNormal : QQNormal := D5.qQNormal_of sSNorm
/- English proof (translation)
The claim follows from `D5.qQHerm`.
-/
theorem qQHerm : QQHerm := D5.qQHerm
/- English proof (translation)
The claim follows from `D5.qQLeading`.
-/
theorem qQLeading : QQLeading := D5.qQLeading
/- English proof (translation)
The claim follows from `D5.qQZeta`.
-/
theorem qQZeta : QQZeta := D5.qQZeta

end Formalism.FourierDecayAlt.P.MAx1

end

section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

def Good (P : Par) (Y : ℂ) : Prop :=
  ∀ π : Ty P, ∀ j ∈ Icc 1 (P.k - 1), ∀ n ∈ ({-2, -1, 0, 1, 2} : Finset ℤ), Y + (rho P π j : ℂ) + (n : ℂ) ≠ 0

def dA (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : A P D := qC P Y • (ggiA P D * kap P D fun π => (xC P π (Y + 1))⁻¹)

def mt (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : A P D := star (lA P D (star Y))

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_eq (f : Ty P → ℂ) :
    kap P D f = Matrix.diagonal fun π => algebraMap ℂ (D.Pr) (f π) := rfl

/- English proof (translation)
The claim follows from `(map_mul _ _ _).symm`.
-/
theorem kap_mul (f g : Ty P → ℂ) : kap P D f * kap P D g = kap P D (f * g) := (map_mul _ _ _).symm

/- English proof (translation)
Rewrite using `[kap_mul, kap_mul, mul_comm]`.
-/
theorem kap_comm (f g : Ty P → ℂ) : kap P D f * kap P D g = kap P D g * kap P D f := by
  rw [kap_mul, kap_mul, mul_comm]

/- English proof (translation)
Rewrite using `[kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `Algebra.commutes _ _`.
-/
theorem kap_diag (f : Ty P → ℂ) (n : Ty P → D.Pr) :
    kap P D f * Matrix.diagonal n = Matrix.diagonal n * kap P D f := by
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

/- English proof (translation)
The claim follows from `kap_diag P D f _`.
-/
theorem kap_sc (f : Ty P → ℂ) (w : D.Pr) : kap P D f * sc P D w = sc P D w * kap P D f := kap_diag P D f _

/- English proof (translation)
The claim follows from `kap_diag P D f _`.
-/
theorem kap_nab (f : Ty P → ℂ) : kap P D f * nabA P D = nabA P D * kap P D f := kap_diag P D f _

/- English proof (translation)
The claim follows from `kap_diag P D f _`.
-/
theorem kap_nabs (f : Ty P → ℂ) : kap P D f * nabsA P D = nabsA P D * kap P D f := kap_diag P D f _

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.star_apply]`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one]`.
-/
theorem star_kap (f : Ty P → ℂ) : star (kap P D f) = kap P D (fun π => star (f π)) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext π
  simp only [Pi.star_apply]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, star_smul, star_one]

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq]`. Use extensionality with `π' π`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `hu : Up P l π π'`. Simplify using `only [SS, Matrix.of_apply, if_pos hu, h π π' hu]`.

Conclude with `(Algebra.commutes _ _)`. Simplify using `[SS, hu]`.
-/
theorem S_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    kap P D g * SS P D l = SS P D l * kap P D f := by
  rw [kap_eq, kap_eq]
  ext π' π
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hu : Up P l π π'
  · simp only [SS, Matrix.of_apply, if_pos hu, h π π' hu]
    exact (Algebra.commutes _ _)
  · simp [SS, hu]

/- English proof (translation)
Establish `h1` using `S_shift P D l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])`. Establish `h2` using `congrArg star h1`. Rewrite `h2` using `[star_mul, star_mul, star_kap, star_kap]`. Simplify using `using h2`.
-/
theorem Ss_shift (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P D l) * kap P D g = kap P D f * star (SS P D l) := by
  have h1 := S_shift P D l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by rw [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa using h2

/- English proof (translation)
Use extensionality with `π' π`. Simplify using `only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]`. Use `split_ifs`. Conclude with `(Algebra.commutes _ _)`. Simplify using the standard rewrite rules.
-/
theorem S_sc (l : ℕ) (w : D.Pr) : SS P D l * sc P D w = sc P D w * SS P D l := by
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

/- English proof (translation)
Establish `h2` using `congrArg star (S_sc P D l (star w))`. Rewrite `h2` using `[star_mul, star_mul, star_sc, star_star]`. Conclude with `h2.symm`.
-/
theorem Ss_sc (l : ℕ) (w : D.Pr) : star (SS P D l) * sc P D w = sc P D w * star (SS P D l) := by
  have h2 := congrArg star (S_sc P D l (star w))
  rw [star_mul, star_mul, star_sc, star_star] at h2
  exact h2.symm

/- English proof (translation)
Rewrite using `[Mx3.rhoUp P l π π' h i hi]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rho_up {l : ℕ} {π π' : Ty P} (h : Up P l π π') {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) :
    (rho P π' i : ℂ) = (rho P π i : ℂ) + if i = l then 1 else 0 := by
  rw [Mx3.rhoUp P l π π' h i hi]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[xC, xEx, Finset.sdiff_singleton_eq_erase]`. Conclude with `(Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) hj).symm`.
-/
theorem xC_split (π : Ty P) (u : ℂ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    xC P π u = (u + (rho P π j : ℂ)) * xEx P {j} π u := by
  rw [xC, xEx, Finset.sdiff_singleton_eq_erase]
  exact (Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) hj).symm

/- English proof (translation)
Establish `h1 : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}).erase j`. Use extensionality with `x`. Simplify using `only [mem_sdiff, mem_insert, mem_singleton, mem_erase]`. The claim follows by propositional logic. Establish `h2 : j ∈ Icc 1 (P.k - 1) \ {l}` using `by simp only [mem_sdiff, mem_singleton]; exact ⟨hj, hlj⟩`.

Rewrite using `[xEx, xEx, h1]`. Conclude with `(Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) h2).symm`.
-/
theorem xEx_split (π : Ty P) (u : ℂ) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hlj : j ≠ l) :
    xEx P {l} π u = (u + (rho P π j : ℂ)) * xEx P {l, j} π u := by
  have h1 : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}).erase j := by
    ext x; simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]; tauto
  have h2 : j ∈ Icc 1 (P.k - 1) \ {l} := by simp only [mem_sdiff, mem_singleton]; exact ⟨hj, hlj⟩
  rw [xEx, xEx, h1]
  exact (Finset.mul_prod_erase _ (fun i => u + (rho P π i : ℂ)) h2).symm

/- English proof (translation)
Unfold `xEx`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi'` using `Finset.mem_sdiff.1 hi`. Establish `hne : i ≠ j` using `fun e => hi'.2 (e ▸ hj)`. Rewrite using `[rho_up P h hi'.1, if_neg hne, add_zero]`.
-/
theorem xEx_up {j : ℕ} {π π' : Ty P} (h : Up P j π π') (ex : Finset ℕ) (hj : j ∈ ex) (u : ℂ) :
    xEx P ex π' u = xEx P ex π u := by
  unfold xEx
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' := Finset.mem_sdiff.1 hi
  have hne : i ≠ j := fun e => hi'.2 (e ▸ hj)
  rw [rho_up P h hi'.1, if_neg hne, add_zero]

def rr (j : ℕ) (u : ℂ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ))⁻¹

def lam (j : ℕ) (u : ℂ) : A P D := kap P D (rr P j u) * SS P D j

def abelian₂ (u : ℂ) : A P D := ∑ j ∈ Icc 1 (P.k - 1), lam P D j u

def lams (j : ℕ) (u : ℂ) : A P D := star (SS P D j) * kap P D (rr P j u)

def Lams (u : ℂ) : A P D := ∑ j ∈ Icc 1 (P.k - 1), lams P D j u

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lA_eq (u : ℂ) : lA P D u = l0A P D u + ggiA P D * abelian₂ P D u := rfl

/- English proof (translation)
Unfold `abelian₂ Lams lam lams`. Rewrite using `[star_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_mul, star_kap]`. Use `congr 2`.

Use function extensionality and compare the values at `π`. Simplify using `[rr]`.
-/
theorem star_Lam (u : ℂ) : star (abelian₂ P D (star u)) = Lams P D u := by
  unfold abelian₂ Lams lam lams
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_mul, star_kap]
  congr 2
  funext π
  simp [rr]

/- English proof (translation)
Simplify using `using h π j hj 0 (by decide)`.
-/
theorem good0 {u : ℂ} (h : Good P u) (π : Ty P) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    u + (rho P π j : ℂ) ≠ 0 := by simpa using h π j hj 0 (by decide)
/- English proof (translation)
Simplify using `using h π j hj 1 (by decide)`.
-/
theorem good1 {u : ℂ} (h : Good P u) (π : Ty P) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    u + (rho P π j : ℂ) + 1 ≠ 0 := by simpa using h π j hj 1 (by decide)
/- English proof (translation)
Simplify `h π j hj (-1) (by decide)` using `[sub_eq_add_neg]`.
-/
theorem goodm1 {u : ℂ} (h : Good P u) (π : Ty P) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) :
    u + (rho P π j : ℂ) - 1 ≠ 0 := by simpa [sub_eq_add_neg] using h π j hj (-1) (by decide)

/- English proof (translation)
Introduce `π j hj n hn h0`. Apply `h π j hj n hn` to reduce the goal to its premises. Use `congrArg star h0` as an intermediate fact. Simplify using `using this`.
-/
theorem good_star {u : ℂ} (h : Good P u) : Good P (star u) := by
  intro π j hj n hn h0
  apply h π j hj n hn
  have := congrArg star h0
  simpa using this

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun _ hj => good0 P h π hj`.
-/
theorem xC_ne {u : ℂ} (h : Good P u) (π : Ty P) : xC P π u ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun _ hj => good0 P h π hj

/- English proof (translation)
The claim follows from `Finset.prod_ne_zero_iff.2 fun j hj => by have := good1 P h π hj intro h0; apply this; rw [← h0]; ring`.
-/
theorem coordinate_shift_ne_zero {u : ℂ} (h : Good P u) (π : Ty P) : xC P π (u + 1) ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun j hj => by
    have := good1 P h π hj
    intro h0; apply this; rw [← h0]; ring

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations
variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Rewrite using `[← mul_assoc, h, mul_assoc]`.
-/
theorem lc {a b : B} (h : a * b = b * a) (x : B) : a * (b * x) = b * (a * x) := by
  rw [← mul_assoc, h, mul_assoc]

/- English proof (translation)
Rewrite using `[← mul_assoc, h, one_mul]`.
-/
theorem lc1 {a b : B} (h : a * b = 1) (x : B) : a * (b * x) = x := by
  rw [← mul_assoc, h, one_mul]

/- English proof (translation)
Rewrite using `[← mul_assoc, h, sub_mul, mul_assoc, mul_assoc]`.
-/
theorem lcs {a b p q : B} (h : a * b = b * a - p * q) (x : B) : a * (b * x) = b * (a * x) - p * (q * x) := by
  rw [← mul_assoc, h, sub_mul, mul_assoc, mul_assoc]

/- English proof (translation)
Rewrite using `[← mul_assoc, h, add_mul, mul_assoc, mul_assoc]`.
-/
theorem lca {a b p q : B} (h : a * b = b * a + p * q) (x : B) : a * (b * x) = b * (a * x) + p * (q * x) := by
  rw [← mul_assoc, h, add_mul, mul_assoc, mul_assoc]

/- English proof (translation)
Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNg, lca hNg, hNX, lc hNX, hgG, lc1 hgG, hGg, lc1 hGg, hcg, lc hcg, hXg, lc hXg, hXG, lc hXG, hXc, lc hXc, hLg, lc hLg, hLg', lc …`. Take the linear combination `(norm := module) h1`.
-/
theorem commutator_identity_one (N c g G X L L' : B) (α β : ℂ)
    (hNg : N * g = g * N + g * c) (hNX : N * X = X * N)
    (hgG : g * G = 1) (hGg : G * g = 1) (hcg : c * g = g * c)
    (hXg : X * g = g * X) (hXG : X * G = G * X) (hXc : X * c = c * X)
    (hLg : L * g = g * L) (hLg' : L' * g = g * L')
    (h1 : (α - β) • (X * L' - L' * X) = -(X * (L - L'))) :
    (α - β) • (g * X * (-N - β • c + G * L') - (-N - β • c + G * L') * (g * X)) =
      -(g * X * ((-N - α • c + G * L) - (-N - β • c + G * L'))) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNg, lca hNg, hNX, lc hNX, hgG, lc1 hgG, hGg, lc1 hGg, hcg, lc hcg,
    hXg, lc hXg, hXG, lc hXG, hXc, lc hXc, hLg, lc hLg, hLg', lc hLg'] at h1 ⊢
  linear_combination (norm := module) h1

/- English proof (translation)
Establish `h1'` using `congrArg (fun x => q • (G * (G * x))) h1`. Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNG, lcs hNG, hNX, lc hNX, hGc, lc hGc, hXG, lc hXG, hXc, lc hXc, hLG, lc hLG, hLG', lc hLG'] at h1' ⊢`. Take the linear combination `(norm := module) h1'`.
-/
theorem commutator_identity_two (N c G X L L' : B) (α β q : ℂ)
    (hNG : N * G = G * N - c * G) (hNX : N * X = X * N)
    (hGc : G * c = c * G)
    (hXG : X * G = G * X) (hXc : X * c = c * X)
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h1 : (α - β) • (X * L' - L' * X) = X * (L - L')) :
    (α - β) • (q • (G * X) * (-N - β • c + G * L') - (-N - β • c + G * L') * (q • (G * X))) =
      q • (G * X) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by
  have h1' := congrArg (fun x => q • (G * (G * x))) h1
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNG, lcs hNG, hNX, lc hNX, hGc, lc hGc,
    hXG, lc hXG, hXc, lc hXc, hLG, lc hLG, hLG', lc hLG'] at h1' ⊢
  linear_combination (norm := module) h1'

/- English proof (translation)
Establish `h3'` using `congrArg (fun x => G * (G * x)) h3`. Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNc, lcs hNc, hNG, lcs hNG, hNL, hNL', hGc, lc hGc, hLc, lc hLc, hLc', lc hLc', hLG, lc hLG, hLG', lc hLG'] at h3' ⊢`. Take the linear combination `(norm := module) h3'`.
-/
theorem raising_pair_relation (N c G L L' : B) (α β : ℂ)
    (hNc : N * c = c * N - c * c) (hNG : N * G = G * N - c * G)
    (hNL : N * L = L * N - c * L) (hNL' : N * L' = L' * N - c * L')
    (hGc : G * c = c * G) (hLc : L * c = c * L) (hLc' : L' * c = c * L')
    (hLG : L * G = G * L) (hLG' : L' * G = G * L')
    (h3 : (α - β) • (L * L' - L' * L) = (L - L') * (L - L')) :
    (α - β) • ((-N - α • c + G * L) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-N - α • c + G * L)) =
      ((-N - α • c + G * L) - (-N - β • c + G * L')) * ((-N - α • c + G * L) - (-N - β • c + G * L')) := by
  have h3' := congrArg (fun x => G * (G * x)) h3
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNc, lcs hNc, hNG, lcs hNG, hNL, hNL', hGc, lc hGc, hLc, lc hLc,
    hLc', lc hLc', hLG, lc hLG, hLG', lc hLG'] at h3' ⊢
  linear_combination (norm := module) h3'

/- English proof (translation)
Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hcurv, hNsc, hNcz, hNG, lcs hNG, hNsG, lca hNsG, hNsL', hNLs, hGc, lc hGc, hGcz, lc hGcz, hczc, lc hczc, hLc', lc hLc', hLcz', l …`. Use `module`.
-/
theorem commutator_identity_four (N Ns c cz G K Ls L' : B) (α β t : ℂ)
    (hcurv : Ns * N = N * Ns + K * (G * G))
    (hNsc : Ns * c = c * Ns + t • (G * G)) (hNcz : N * cz = cz * N - t • (G * G))
    (hNG : N * G = G * N - c * G) (hNsG : Ns * G = G * Ns + cz * G)
    (hNsL' : Ns * L' = L' * Ns - cz * L') (hNLs : N * Ls = Ls * N + c * Ls)
    (hGc : G * c = c * G) (hGcz : G * cz = cz * G) (hczc : cz * c = c * cz)
    (hLc' : L' * c = c * L') (hLcz' : L' * cz = cz * L') (hLG' : L' * G = G * L')
    (hLsc : Ls * c = c * Ls) (hLscz : Ls * cz = cz * Ls) (hLsG : Ls * G = G * Ls) :
    (-Ns - α • cz + G * Ls) * (-N - β • c + G * L') - (-N - β • c + G * L') * (-Ns - α • cz + G * Ls) =
      K * (G * G) + ((α + β) * t) • (G * G) + G * (G * (Ls * L' - L' * Ls)) := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hcurv, hNsc, hNcz, hNG, lcs hNG, hNsG, lca hNsG, hNsL', hNLs,
    hGc, lc hGc, hGcz, lc hGcz, hczc, lc hczc, hLc', lc hLc', hLcz', lc hLcz', hLG', lc hLG',
    hLsc, lc hLsc, hLscz, lc hLscz, hLsG, lc hLsG]
  module

/- English proof (translation)
Simplify using `only [mul_add, mul_assoc, lc hXG, lc1 hgG]`.
-/
theorem diagonal_lowering_absorb (g G X l0 L : B) (hgG : g * G = 1) (hXG : X * G = G * X) :
    g * X * (l0 + G * L) = g * X * l0 + X * L := by
  simp only [mul_add, mul_assoc, lc hXG, lc1 hgG]

/- English proof (translation)
Simplify using `only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNsg, lcs hNsg, hNsX, hGg, lc1 hGg, hczg, lc hczg, hczX, hLsg, lc hLsg]`. Use `module`.
-/
theorem raising_operator_absorb (Ns cz g G X Ls : B) (α : ℂ)
    (hNsg : Ns * g = g * Ns - g * cz) (hNsX : Ns * X = X * Ns) (hGg : G * g = 1) (hczg : cz * g = g * cz)
    (hczX : cz * X = X * cz) (hLsg : Ls * g = g * Ls) :
    (-Ns - α • cz + G * Ls) * (g * X) = g * X * (-Ns - (α - 1) • cz) + Ls * X := by
  simp only [mul_add, add_mul, mul_sub, sub_mul, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, smul_add,
    smul_sub, smul_neg, smul_smul, mul_assoc, neg_neg, hNsg, lcs hNsg, hNsX, hGg, lc1 hGg, hczg, lc hczg, hczX, hLsg, lc hLsg]
  module

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.GA

section Gauss

variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Rewrite using `[← h, smul_smul, inv_mul_cancel₀ hD, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem solve_right {D : ℂ} (hD : D ≠ 0) {x y z : B} (h : D • (x - y) = z) : y = x - D⁻¹ • z := by
  rw [← h, smul_smul, inv_mul_cancel₀ hD, one_smul]; abel

/- English proof (translation)
Rewrite using `[← h, smul_smul, inv_mul_cancel₀ hD, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem solve_left {D : ℂ} (hD : D ≠ 0) {x y z : B} (h : D • (x - y) = z) : x = y + D⁻¹ • z := by
  rw [← h, smul_smul, inv_mul_cancel₀ hD, one_smul]; abel

/- English proof (translation)
Rewrite using `[← mul_assoc, h]`.
-/
theorem assoc_var {a b R : B} (h : a * b = R) (x : B) : a * (b * x) = R * x := by
  rw [← mul_assoc, h]

/- English proof (translation)
Rewrite using `[← h]`. Simplify using `only [mul_assoc]`.
-/
theorem mul_assoc_four_right {a b c e R : B} (h : a * (b * (c * e)) = R) (x : B) : a * (b * (c * (e * x))) = R * x := by
  rw [← h]; simp only [mul_assoc]

/- English proof (translation)
Establish `hm1 : D - 1 ≠ 0` using `sub_ne_zero.mpr hD1`. Establish `hp1 : D + 1 ≠ 0` using `by intro h; exact hD2 (by linear_combination h)`. Establish `r1 : l' * τ = τ * l' - D⁻¹ • -(τ * (l - l'))` using `solve_right hD0 D1`. Establish `r2 : l * τ' = τ' * l - D⁻¹ • -(τ' * (l - l'))` using `solve_right hD0 D1s`. Establish `r3 : l' * d = d * l' - D⁻¹ • (d * (l - l'))` using `solve_right hD0 D2`.

Establish `r4 : l * d' = d' * l - D⁻¹ • (d' * (l - l'))` using `solve_right hD0 D2s`. Establish `r5 : τ * m' = m' * τ + D⁻¹ • ((m - m') * τ)` using `solve_left hD0 E1`. Establish `r6 : τ' * m = m * τ' + D⁻¹ • ((m - m') * τ')` using `solve_left hD0 TwistedContraction`. Establish `r7 : d * m' = m' * d + D⁻¹ • -((m - m') * d)` using `solve_left hD0 E2`. Establish `r8 : d' * m = m * d' + D⁻¹ • -((m - m') * d')` using `solve_left hD0 E2VanishingOtherColumns`.

Establish `s1 : τ' * (l' * (m * τ)) = τ' * (m * (l' * τ)) - D⁻¹ • (d' * τ - τ' * d)`. Use `solve_right hD0 D4` as an intermediate fact. Simplify `this` using `only [mul_assoc]`. Establish `s2 : τ * (l * (m' * τ')) = τ * (m' * (l * τ')) - D⁻¹ • (τ * d' - d * τ')`. Use `solve_right hD0 D4s` as an intermediate fact.

Simplify `this` using `only [mul_assoc]`. Establish `o1 : l' * l = (D - 1)⁻¹ • ((D + 1) • (l * l') - l * l - l' * l')`. Establish `h : (D - 1) • (l' * l) = (D + 1) • (l * l') - l * l - l' * l'`. Establish `h2 : D • (l * l') - D • (l' * l) = l * l - l * l' - l' * l + l' * l'`. Rewrite using `[← smul_sub, D3]`.

Use `noncomm_ring`. Rewrite using `[sub_smul, add_smul, one_smul, one_smul]`. Establish `h3 : D • (l' * l) = D • (l * l') - (l * l - l * l' - l' * l + l' * l')` using `by rw [← h2]; abel`. Rewrite using `[h3]`. Normalize the expressions using the abelian group laws.

Rewrite using `[← h, smul_smul, inv_mul_cancel₀ hm1, one_smul]`. Establish `o2 : m' * m = (D + 1)⁻¹ • ((D - 1) • (m * m') + m * m + m' * m')`. Establish `h : (D + 1) • (m' * m) = (D - 1) • (m * m') + m * m + m' * m'`. Establish `h2 : D • (m * m') - D • (m' * m) = -(m * m - m * m' - m' * m + m' * m')`. Rewrite using `[← smul_sub, E3]`.

Use `noncomm_ring`. Rewrite using `[sub_smul, add_smul, one_smul, one_smul]`. Establish `h3 : D • (m' * m) = D • (m * m') + (m * m - m * m' - m' * m + m' * m')`. Establish `: D • (m' * m) = D • (m * m') - (D • (m * m') - D • (m' * m))` using `by abel`. Rewrite using `[this, h2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h3]`. Normalize the expressions using the abelian group laws. Rewrite using `[← h, smul_smul, inv_mul_cancel₀ hp1, one_smul]`. Introduce `i j k n`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases n <;>`. Simplify using `only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const, mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_add, smul_sub …`. Apply the tactic sequence `all_goals (match_scalars <;> field_simp <;> ring)`.
-/
theorem gauss_rtt (D : ℂ) (hD0 : D ≠ 0) (hD1 : D ≠ 1) (hD2 : D ≠ -1) (τ τ' d d' l l' m m' : B)
    (c1 : τ' * τ = τ * τ') (c2 : d' * d = d * d') (c3 : d' * τ = τ * d') (c4 : d * τ' = τ' * d)
    (D1 : D • (τ * l' - l' * τ) = -(τ * (l - l'))) (D1s : D • (τ' * l - l * τ') = -(τ' * (l - l')))
    (D2 : D • (d * l' - l' * d) = d * (l - l')) (D2s : D • (d' * l - l * d') = d' * (l - l'))
    (E1 : D • (τ * m' - m' * τ) = (m - m') * τ) (TwistedContraction : D • (τ' * m - m * τ') = (m - m') * τ')
    (E2 : D • (d * m' - m' * d) = -((m - m') * d)) (E2VanishingOtherColumns : D • (d' * m - m * d') = -((m - m') * d'))
    (D3 : D • (l * l' - l' * l) = (l - l') * (l - l')) (E3 : D • (m * m' - m' * m) = -((m - m') * (m - m')))
    (D4 : D • (τ' * m * l' * τ - τ' * l' * m * τ) = d' * τ - τ' * d)
    (D4s : D • (τ * m' * l * τ' - τ * l * m' * τ') = τ * d' - d * τ') :
    ∀ i j k n : Fin 2,
      D • ((!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j) =
        (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) i n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i n := by
  have hm1 : D - 1 ≠ 0 := sub_ne_zero.mpr hD1
  have hp1 : D + 1 ≠ 0 := by intro h; exact hD2 (by linear_combination h)
  have r1 : l' * τ = τ * l' - D⁻¹ • -(τ * (l - l')) := solve_right hD0 D1
  have r2 : l * τ' = τ' * l - D⁻¹ • -(τ' * (l - l')) := solve_right hD0 D1s
  have r3 : l' * d = d * l' - D⁻¹ • (d * (l - l')) := solve_right hD0 D2
  have r4 : l * d' = d' * l - D⁻¹ • (d' * (l - l')) := solve_right hD0 D2s
  have r5 : τ * m' = m' * τ + D⁻¹ • ((m - m') * τ) := solve_left hD0 E1
  have r6 : τ' * m = m * τ' + D⁻¹ • ((m - m') * τ') := solve_left hD0 TwistedContraction
  have r7 : d * m' = m' * d + D⁻¹ • -((m - m') * d) := solve_left hD0 E2
  have r8 : d' * m = m * d' + D⁻¹ • -((m - m') * d') := solve_left hD0 E2VanishingOtherColumns
  have s1 : τ' * (l' * (m * τ)) = τ' * (m * (l' * τ)) - D⁻¹ • (d' * τ - τ' * d) := by
    have := solve_right hD0 D4
    simpa only [mul_assoc] using this
  have s2 : τ * (l * (m' * τ')) = τ * (m' * (l * τ')) - D⁻¹ • (τ * d' - d * τ') := by
    have := solve_right hD0 D4s
    simpa only [mul_assoc] using this
  have o1 : l' * l = (D - 1)⁻¹ • ((D + 1) • (l * l') - l * l - l' * l') := by
    have h : (D - 1) • (l' * l) = (D + 1) • (l * l') - l * l - l' * l' := by
      have h2 : D • (l * l') - D • (l' * l) = l * l - l * l' - l' * l + l' * l' := by
        rw [← smul_sub, D3]; noncomm_ring
      rw [sub_smul, add_smul, one_smul, one_smul]
      have h3 : D • (l' * l) = D • (l * l') - (l * l - l * l' - l' * l + l' * l') := by rw [← h2]; abel
      rw [h3]; abel
    rw [← h, smul_smul, inv_mul_cancel₀ hm1, one_smul]
  have o2 : m' * m = (D + 1)⁻¹ • ((D - 1) • (m * m') + m * m + m' * m') := by
    have h : (D + 1) • (m' * m) = (D - 1) • (m * m') + m * m + m' * m' := by
      have h2 : D • (m * m') - D • (m' * m) = -(m * m - m * m' - m' * m + m' * m') := by
        rw [← smul_sub, E3]; noncomm_ring
      rw [sub_smul, add_smul, one_smul, one_smul]
      have h3 : D • (m' * m) = D • (m * m') + (m * m - m * m' - m' * m + m' * m') := by
        have : D • (m' * m) = D • (m * m') - (D • (m * m') - D • (m' * m)) := by abel
        rw [this, h2]; abel
      rw [h3]; abel
    rw [← h, smul_smul, inv_mul_cancel₀ hp1, one_smul]
  intro i j k n
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases n <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_add, smul_sub, smul_neg, smul_smul,
    smul_mul_assoc, mul_smul_comm, mul_assoc,
    s1, s2, mul_assoc_four_right s1, mul_assoc_four_right s2,
    r1, r2, r3, r4, r5, r6, r7, r8, assoc_var r1, assoc_var r2, assoc_var r3, assoc_var r4,
    assoc_var r5, assoc_var r6, assoc_var r7, assoc_var r8, o1, o2, assoc_var o1, assoc_var o2,
    c1, c2, c3, c4, assoc_var c1, assoc_var c2, assoc_var c3, assoc_var c4]
  all_goals (match_scalars <;> field_simp <;> ring)

end Gauss

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.GA

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.WB

open Matrix Finset Polynomial  Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

def pX (I : Finset ℕ) (ρ : ℕ → ℂ) : ℂ[X] := ∏ i ∈ I, (X + C (ρ i))

/- English proof (translation)
Simplify using `[pX, eval_prod]`.
-/
theorem pX_eval (I : Finset ℕ) (ρ : ℕ → ℂ) (u : ℂ) : (pX I ρ).eval u = ∏ i ∈ I, (u + ρ i) := by
  simp [pX, eval_prod]

/- English proof (translation)
Unfold `pX`. Conclude with `(Finset.mul_prod_erase I _ hl).symm`.
-/
theorem pX_erase (I : Finset ℕ) (ρ : ℕ → ℂ) {l : ℕ} (hl : l ∈ I) :
    pX I ρ = (X + C (ρ l)) * pX (I.erase l) ρ := by
  unfold pX; exact (Finset.mul_prod_erase I _ hl).symm

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)`.
-/
theorem pX_monic (I : Finset ℕ) (ρ : ℕ → ℂ) : (pX I ρ).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

/- English proof (translation)
Unfold `pX`. Rewrite using `[natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]`. Simplify using the standard rewrite rules.
-/
theorem pX_natDegree (I : Finset ℕ) (ρ : ℕ → ℂ) : (pX I ρ).natDegree = I.card := by
  unfold pX; rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]; simp

/- English proof (translation)
Unfold `pX`. Rewrite using `[Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]`. Simplify using the standard rewrite rules.
-/
theorem pX_nextCoeff (I : Finset ℕ) (ρ : ℕ → ℂ) : (pX I ρ).nextCoeff = ∑ i ∈ I, ρ i := by
  unfold pX; rw [Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]; simp

def W1 (I : Finset ℕ) (ρ : ℕ → ℂ) (q w : ℂ[X]) (N : ℕ → ℂ) : Prop :=
  w * pX I (fun i => ρ i + 1) = q + ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) (fun i => ρ i + 1))

/- English proof (translation)
Use `congrArg (Polynomial.eval u) h` as an intermediate fact. Simplify `this` using `[eval_finsetSum, pX_eval]`.
-/
theorem W1.eval {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N) (u : ℂ) :
    w.eval u * ∏ i ∈ I, (u + (ρ i + 1)) = q.eval u +
      ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) := by
  have := congrArg (Polynomial.eval u) h
  simpa [eval_finsetSum, pX_eval] using this

/- English proof (translation)
Establish `h1` using `h.eval (-ρ l)`. Rewrite `h1` using `[← Finset.mul_prod_erase I _ hl, Finset.sum_eq_single l]`. Establish `e1 : ∏ j ∈ I.erase l, (-ρ l + (ρ j + 1)) = ∏ j ∈ I.erase l, (ρ j - ρ l + 1)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Establish `e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Rewrite `h1` using `[e1, e2]`.

Apply `mul_right_cancel₀ hE1` to reduce the goal to its premises. Take the linear combination `h1 + hNd`. Introduce `m _ hml`. Establish `: ∏ j ∈ I.erase m, (-ρ l + ρ j) = 0` using `Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd hl h`.
-/
theorem rootA {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) {l : ℕ} (hl : l ∈ I)
    (hE1 : ∏ j ∈ I.erase l, (ρ j - ρ l + 1) ≠ 0)
    (hNd : Nd l * ((∏ j ∈ I.erase l, (ρ j - ρ l + 1)) * ∏ j ∈ I.erase l, (ρ j - ρ l)) = -(q.eval (-ρ l))) :
    w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
  have h1 := h.eval (-ρ l)
  rw [← Finset.mul_prod_erase I _ hl, Finset.sum_eq_single l] at h1
  · have e1 : ∏ j ∈ I.erase l, (-ρ l + (ρ j + 1)) = ∏ j ∈ I.erase l, (ρ j - ρ l + 1) :=
      Finset.prod_congr rfl (fun j _ => by ring)
    have e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l) :=
      Finset.prod_congr rfl (fun j _ => by ring)
    rw [e1, e2] at h1
    apply mul_right_cancel₀ hE1
    linear_combination h1 + hNd
  · intro m _ hml
    have : ∏ j ∈ I.erase m, (-ρ l + ρ j) = 0 :=
      Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)
    rw [this]; simp
  · intro h; exact absurd hl h

/- English proof (translation)
Use `set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1`. Establish `hx1 : pX I ρ1 = (X + C (ρ l)) * pX (I.erase j0) ρ1`. Rewrite using `[pX_erase I ρ1 hj0, hρ1]`. Simplify using `only [hρ]`. Establish `hF : pX (I.erase j0) ρ1 = (X + C (ρ l + 1)) * pX ((I.erase j0).erase l) ρ1` using `pX_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, hl⟩)`.

Establish `hE : pX (I.erase l) ρ1 = (X + C (ρ l)) * pX ((I.erase j0).erase l) ρ1`. Rewrite using `[pX_erase (I.erase l) ρ1 (Finset.mem_erase.2 ⟨hne, hj0⟩), Finset.erase_right_comm, hρ1]`. Simplify using `only [hρ]`. Establish `hdiv : (X + C (ρ l)) ^ 2 ∣ q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1)`. Use `dvd_add hq (Finset.dvd_sum fun m hm => ?_)` and prove the remaining obligations.

Distinguish the cases in `hm0 : m = j0`. Rewrite using `[hm0, hN0]`. Simplify using the standard rewrite rules. Establish `hm'` using `Finset.mem_erase.1 hm`. Rewrite using `[pX_erase (I.erase m) ρ (Finset.mem_erase.2 ⟨fun e => hm'.1 e.symm, hl⟩), pX_erase (I.erase m) ρ1 (Finset.mem_erase.2 ⟨fun e => hm0 e.symm, hj0⟩)]`.

Establish `: (ρ1 j0) = ρ l` using `hρ`. Rewrite using `[this]`. Conclude with `⟨C (N m) * (pX ((I.erase m).erase l) ρ * pX ((I.erase m).erase j0) ρ1), by ring⟩`. Take `⟨Aq, hA⟩` from `hdiv`. Establish `h2 : w * pX I ρ1 = (q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1)) + C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1)`.

Use `h` as an intermediate fact. Unfold `W1 at this`. Rewrite using `[this, ← Finset.add_sum_erase I _ hl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[hA, hx1, hE]`.

Establish `h3 : w * pX (I.erase j0) ρ1 = (X + C (ρ l)) * Aq + C (N l) * (pX (I.erase l) ρ * pX ((I.erase j0).erase l) ρ1)`. Apply `mul_left_cancel₀ (monic_X_add_C (ρ l)).ne_zero` to reduce the goal to its premises. Take the linear combination `h2`. Rewrite `h3` using `[hF]`. Establish `h4` using `congrArg (Polynomial.eval (-ρ l)) h3`.

Simplify using `only [eval_mul, eval_add, eval_X, eval_C, pX_eval] at h4`. Establish `hG : ∏ j ∈ (I.erase j0).erase l, (-ρ l + ρ1 j) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j hj h0`. Establish `hj'` using `Finset.mem_erase.1 hj`.

Establish `hj''` using `Finset.mem_erase.1 hj'.2`. Apply `hj''.1` to reduce the goal to its premises. Apply `hinj j hj''.2 j0 hj0` to reduce the goal to its premises. Establish `: ρ1 j = ρ j + 1` using `rfl`. Rewrite `h0` using `[this]`.

Take the linear combination `h0 - hρ`. Establish `e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Rewrite `h4` using `[e2]`. Apply `mul_right_cancel₀ hG` to reduce the goal to its premises. Take the linear combination `h4`.
-/
theorem rootB {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (h : W1 I ρ q w N)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {l j0 : ℕ} (hl : l ∈ I) (hj0 : j0 ∈ I) (hne : j0 ≠ l)
    (hρ : ρ j0 + 1 = ρ l) (hq : (X + C (ρ l)) ^ 2 ∣ q) (hN0 : N j0 = 0) :
    w.eval (-ρ l) = N l * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
  set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1
  have hx1 : pX I ρ1 = (X + C (ρ l)) * pX (I.erase j0) ρ1 := by
    rw [pX_erase I ρ1 hj0, hρ1]; simp only [hρ]
  have hF : pX (I.erase j0) ρ1 = (X + C (ρ l + 1)) * pX ((I.erase j0).erase l) ρ1 :=
    pX_erase _ _ (Finset.mem_erase.2 ⟨hne.symm, hl⟩)
  have hE : pX (I.erase l) ρ1 = (X + C (ρ l)) * pX ((I.erase j0).erase l) ρ1 := by
    rw [pX_erase (I.erase l) ρ1 (Finset.mem_erase.2 ⟨hne, hj0⟩), Finset.erase_right_comm, hρ1]; simp only [hρ]
  have hdiv : (X + C (ρ l)) ^ 2 ∣ q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1) := by
    refine dvd_add hq (Finset.dvd_sum fun m hm => ?_)
    by_cases hm0 : m = j0
    · rw [hm0, hN0]; simp
    · have hm' := Finset.mem_erase.1 hm
      rw [pX_erase (I.erase m) ρ (Finset.mem_erase.2 ⟨fun e => hm'.1 e.symm, hl⟩),
        pX_erase (I.erase m) ρ1 (Finset.mem_erase.2 ⟨fun e => hm0 e.symm, hj0⟩)]
      have : (ρ1 j0) = ρ l := hρ
      rw [this]
      exact ⟨C (N m) * (pX ((I.erase m).erase l) ρ * pX ((I.erase m).erase j0) ρ1), by ring⟩
  obtain ⟨Aq, hA⟩ := hdiv
  have h2 : w * pX I ρ1 = (q + ∑ m ∈ I.erase l, C (N m) * (pX (I.erase m) ρ * pX (I.erase m) ρ1)) +
      C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) := by
    have := h
    unfold W1 at this
    rw [this, ← Finset.add_sum_erase I _ hl]; ring
  rw [hA, hx1, hE] at h2
  have h3 : w * pX (I.erase j0) ρ1 = (X + C (ρ l)) * Aq + C (N l) * (pX (I.erase l) ρ * pX ((I.erase j0).erase l) ρ1) := by
    apply mul_left_cancel₀ (monic_X_add_C (ρ l)).ne_zero
    linear_combination h2
  rw [hF] at h3
  have h4 := congrArg (Polynomial.eval (-ρ l)) h3
  simp only [eval_mul, eval_add, eval_X, eval_C, pX_eval] at h4
  have hG : ∏ j ∈ (I.erase j0).erase l, (-ρ l + ρ1 j) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj h0
    have hj' := Finset.mem_erase.1 hj
    have hj'' := Finset.mem_erase.1 hj'.2
    apply hj''.1
    apply hinj j hj''.2 j0 hj0
    have : ρ1 j = ρ j + 1 := rfl
    rw [this] at h0
    linear_combination h0 - hρ
  have e2 : ∏ j ∈ I.erase l, (-ρ l + ρ j) = ∏ j ∈ I.erase l, (ρ j - ρ l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e2] at h4
  apply mul_right_cancel₀ hG
  linear_combination h4

/- English proof (translation)
Establish `hd : (p + r).natDegree = p.natDegree` using `natDegree_add_eq_left_of_natDegree_lt (by omega)`. Use `⟨hp.add_of_left (degree_lt_degree (by omega)), hd, ?_⟩` and prove the remaining obligations. Rewrite using `[nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), hd, coeff_add, coeff_eq_zero_of_natDegree_lt (p := r) (by omega), add_zero]`.
-/
theorem add_low {p r : ℂ[X]} (hp : p.Monic) (hr : r.natDegree + 1 < p.natDegree) :
    (p + r).Monic ∧ (p + r).natDegree = p.natDegree ∧ (p + r).nextCoeff = p.nextCoeff := by
  have hd : (p + r).natDegree = p.natDegree := natDegree_add_eq_left_of_natDegree_lt (by omega)
  refine ⟨hp.add_of_left (degree_lt_degree (by omega)), hd, ?_⟩
  rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), hd, coeff_add,
    coeff_eq_zero_of_natDegree_lt (p := r) (by omega), add_zero]

/- English proof (translation)
Unfold `pX`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `i hi j hj hij show IsCoprime (X + C (ρ i)) (X + C (ρ j))`. Establish `e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a)` using `by intro a; simp`. Rewrite using `[e, e]`.

Apply `isCoprime_X_sub_C_of_isUnit_sub` to reduce the goal to its premises. Apply `IsUnit.mk0` to reduce the goal to its premises. Introduce `h0`. Conclude with `hij (hinj i hi j hj (by linear_combination -h0))`. Introduce `l hl`.

Establish `e : (X + C (ρ l) : ℂ[X]) = X - C (-(ρ l))` using `by rw [C_neg, sub_neg_eq_add]`. Rewrite using `[e, dvd_iff_isRoot, IsRoot.def]`. Conclude with `hR l hl`.
-/
theorem pX_dvd {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {R : ℂ[X]}
    (hR : ∀ l ∈ I, R.eval (-ρ l) = 0) : pX I ρ ∣ R := by
  unfold pX
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    show IsCoprime (X + C (ρ i)) (X + C (ρ j))
    have e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a) := by intro a; simp
    rw [e, e]
    apply isCoprime_X_sub_C_of_isUnit_sub
    apply IsUnit.mk0
    intro h0
    exact hij (hinj i hi j hj (by linear_combination -h0))
  · intro l hl
    have e : (X + C (ρ l) : ℂ[X]) = X - C (-(ρ l)) := by rw [C_neg, sub_neg_eq_add]
    rw [e, dvd_iff_isRoot, IsRoot.def]
    exact hR l hl

/- English proof (translation)
Use `set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1`. Use `set S1 : ℂ[X] := ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) with hS1`. Use `set S2 : ℂ[X] := ∑ l ∈ I, C (N l - Nd l) * pX (I.erase l) ρ with hS2`. Establish `hcc : (C c⁻¹ * C c : ℂ[X]) = 1` using `by rw [← C_mul, inv_mul_cancel₀ hc, C_1]`. Establish `dS1 : (C c⁻¹ * S1).natDegree ≤ I.card + I.card`.

Use `(natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)` and prove the remaining obligations. Use `(natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)` and prove the remaining obligations. Rewrite using `[pX_natDegree, pX_natDegree]`. Conclude with `add_le_add (Finset.card_erase_le) (Finset.card_erase_le)`. Establish `dS2 : (-(C c⁻¹ * S2)).natDegree ≤ I.card`.

Rewrite using `[natDegree_neg]`. Use `(natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)` and prove the remaining obligations. Use `(natDegree_C_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[pX_natDegree]`. Conclude with `Finset.card_erase_le`.

Establish `hM : (C c⁻¹ * w) * pX I ρ1 = q1 + C c⁻¹ * S1`. Use `h` as an intermediate fact. Unfold `W1 at this`. Combine the equalities or inequalities in the displayed calculation. Take `⟨m1, m2, m3⟩` from `add_low (p := q1) (r := C c⁻¹ * S1) hq1 (by omega)`.

Rewrite `m1`, `m2`, `m3` using `[← hM]`. Establish `hw1 : (C c⁻¹ * w).Monic` using `Monic.of_mul_monic_right (pX_monic I ρ1) m1`. Rewrite `m2` using `[hw1.natDegree_mul (pX_monic I ρ1), pX_natDegree]`. Rewrite `m3` using `[hw1.nextCoeff_mul (pX_monic I ρ1), pX_nextCoeff]`. Take `⟨r1, r2, r3⟩` from `add_low (p := C c⁻¹ * w) (r := -(C c⁻¹ * S2)) hw1 (by omega)`.

Establish `hdvd : pX I ρ ∣ C c⁻¹ * w + -(C c⁻¹ * S2)`. Apply `pX_dvd hinj` to reduce the goal to its premises. Introduce `l hl`. Establish `: S2.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l)`. Rewrite using `[hS2, eval_finsetSum, Finset.sum_eq_single l]`.

Rewrite using `[eval_mul, eval_C, pX_eval]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl (fun j _ => by ring)`. Introduce `m _ hml`. Rewrite using `[eval_mul, eval_C, pX_eval, Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)]`.

Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd hl h`. Simplify using `only [eval_add, eval_neg, eval_mul, eval_C, this, hroot l hl]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨Q, hQ⟩` from `hdvd`. Rewrite `r1`, `r2`, `r3` using `[hQ]`. Establish `hQm : Q.Monic` using `Monic.of_mul_monic_left (pX_monic I ρ) r1`. Rewrite `r2` using `[(pX_monic I ρ).natDegree_mul hQm, pX_natDegree]`. Rewrite `r3` using `[(pX_monic I ρ).nextCoeff_mul hQm, pX_nextCoeff]`.

Establish `hQd : Q.natDegree = 2` using `by omega`. Establish `hQ2 : Q.coeff 2 = 1` using `by rw [← hQd]; exact hQm`. Establish `hQ1 : Q.coeff 1 = Q.nextCoeff` using `by rw [nextCoeff_of_natDegree_pos (by omega), hQd]`. Use `⟨c * Q.coeff 0, fun u => ?_⟩` and prove the remaining obligations. Establish `hQe : Q.eval u = Q.coeff 0 + Q.nextCoeff * u + u ^ 2`.

Rewrite using `[eval_eq_sum_range, hQd]`. Simplify using `[Finset.sum_range_succ, hQ2, hQ1]`. Establish `hS2e : S2.eval u = ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j)`. Rewrite using `[hS2, eval_finsetSum]`. Conclude with `Finset.sum_congr rfl (fun l _ => by rw [eval_mul, eval_C, pX_eval])`.

Establish `h5` using `congrArg (Polynomial.eval u) hQ`. Simplify using `only [eval_add, eval_neg, eval_mul, eval_C, pX_eval, hQe, hS2e] at h5`. Rewrite `h5`, the goal using `[← hS2e]`. Establish `hn : Q.nextCoeff = q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i`. Establish `: ∑ i ∈ I, ρ1 i = ∑ i ∈ I, (ρ i + 1)` using `rfl`.

Rewrite `m3` using `[this]`. Take the linear combination `r3 + m3`. Rewrite using `[← hn]`. Establish `: w.eval u = c * (c⁻¹ * w.eval u)` using `by field_simp`. Rewrite using `[this]`.

Establish `h6 : c⁻¹ * w.eval u = (∏ i ∈ I, (u + ρ i)) * (Q.coeff 0 + Q.nextCoeff * u + u ^ 2) + c⁻¹ * S2.eval u`. Take the linear combination `h5`. Rewrite using `[h6]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad {I : Finset ℕ} {ρ : ℕ → ℂ} (hinj : ∀ i ∈ I, ∀ j ∈ I, ρ i = ρ j → i = j) {q1 w : ℂ[X]} (hq1 : q1.Monic)
    (hdeg : q1.natDegree = 2 * I.card + 2) {c : ℂ} (hc : c ≠ 0) {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ (C c * q1) w N)
    (hroot : ∀ l ∈ I, w.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l)) :
    ∃ c0 : ℂ, ∀ u : ℂ, w.eval u = (∏ i ∈ I, (u + ρ i)) *
      (c * (u ^ 2 + (q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i) * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by
  set ρ1 : ℕ → ℂ := fun i => ρ i + 1 with hρ1
  set S1 : ℂ[X] := ∑ l ∈ I, C (N l) * (pX (I.erase l) ρ * pX (I.erase l) ρ1) with hS1
  set S2 : ℂ[X] := ∑ l ∈ I, C (N l - Nd l) * pX (I.erase l) ρ with hS2
  have hcc : (C c⁻¹ * C c : ℂ[X]) = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]
  have dS1 : (C c⁻¹ * S1).natDegree ≤ I.card + I.card := by
    refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    rw [pX_natDegree, pX_natDegree]
    exact add_le_add (Finset.card_erase_le) (Finset.card_erase_le)
  have dS2 : (-(C c⁻¹ * S2)).natDegree ≤ I.card := by
    rw [natDegree_neg]
    refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun l _ => ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [pX_natDegree]
    exact Finset.card_erase_le
  have hM : (C c⁻¹ * w) * pX I ρ1 = q1 + C c⁻¹ * S1 := by
    have := h
    unfold W1 at this
    calc (C c⁻¹ * w) * pX I ρ1 = C c⁻¹ * (w * pX I ρ1) := by ring
      _ = C c⁻¹ * (C c * q1 + S1) := by rw [this]
      _ = (C c⁻¹ * C c) * q1 + C c⁻¹ * S1 := by ring
      _ = q1 + C c⁻¹ * S1 := by rw [hcc, one_mul]
  obtain ⟨m1, m2, m3⟩ := add_low (p := q1) (r := C c⁻¹ * S1) hq1 (by omega)
  rw [← hM] at m1 m2 m3
  have hw1 : (C c⁻¹ * w).Monic := Monic.of_mul_monic_right (pX_monic I ρ1) m1
  rw [hw1.natDegree_mul (pX_monic I ρ1), pX_natDegree] at m2
  rw [hw1.nextCoeff_mul (pX_monic I ρ1), pX_nextCoeff] at m3
  obtain ⟨r1, r2, r3⟩ := add_low (p := C c⁻¹ * w) (r := -(C c⁻¹ * S2)) hw1 (by omega)
  have hdvd : pX I ρ ∣ C c⁻¹ * w + -(C c⁻¹ * S2) := by
    apply pX_dvd hinj
    intro l hl
    have : S2.eval (-ρ l) = (N l - Nd l) * ∏ j ∈ I.erase l, (ρ j - ρ l) := by
      rw [hS2, eval_finsetSum, Finset.sum_eq_single l]
      · rw [eval_mul, eval_C, pX_eval]
        congr 1
        exact Finset.prod_congr rfl (fun j _ => by ring)
      · intro m _ hml
        rw [eval_mul, eval_C, pX_eval, Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hml h.symm, hl⟩) (by ring)]
        simp
      · intro h; exact absurd hl h
    simp only [eval_add, eval_neg, eval_mul, eval_C, this, hroot l hl]
    ring
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ] at r1 r2 r3
  have hQm : Q.Monic := Monic.of_mul_monic_left (pX_monic I ρ) r1
  rw [(pX_monic I ρ).natDegree_mul hQm, pX_natDegree] at r2
  rw [(pX_monic I ρ).nextCoeff_mul hQm, pX_nextCoeff] at r3
  have hQd : Q.natDegree = 2 := by omega
  have hQ2 : Q.coeff 2 = 1 := by rw [← hQd]; exact hQm
  have hQ1 : Q.coeff 1 = Q.nextCoeff := by rw [nextCoeff_of_natDegree_pos (by omega), hQd]
  refine ⟨c * Q.coeff 0, fun u => ?_⟩
  have hQe : Q.eval u = Q.coeff 0 + Q.nextCoeff * u + u ^ 2 := by
    rw [eval_eq_sum_range, hQd]
    simp [Finset.sum_range_succ, hQ2, hQ1]
  have hS2e : S2.eval u = ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) := by
    rw [hS2, eval_finsetSum]
    exact Finset.sum_congr rfl (fun l _ => by rw [eval_mul, eval_C, pX_eval])
  have h5 := congrArg (Polynomial.eval u) hQ
  simp only [eval_add, eval_neg, eval_mul, eval_C, pX_eval, hQe, hS2e] at h5
  rw [← hS2e] at h5 ⊢
  have hn : Q.nextCoeff = q1.nextCoeff - ∑ i ∈ I, (ρ i + 1) - ∑ i ∈ I, ρ i := by
    have : ∑ i ∈ I, ρ1 i = ∑ i ∈ I, (ρ i + 1) := rfl
    rw [this] at m3
    linear_combination r3 + m3
  rw [← hn]
  have : w.eval u = c * (c⁻¹ * w.eval u) := by field_simp
  rw [this]
  have h6 : c⁻¹ * w.eval u = (∏ i ∈ I, (u + ρ i)) * (Q.coeff 0 + Q.nextCoeff * u + u ^ 2) + c⁻¹ * S2.eval u := by
    linear_combination h5
  rw [h6]
  field_simp
  ring

/- English proof (translation)
Establish `hx0 : ∏ i ∈ I, (u + ρ i) ≠ 0` using `Finset.prod_ne_zero_iff.2 h0`. Establish `hx1 : ∏ i ∈ I, (u + (ρ i + 1)) ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact h1 i hi)`. Establish `s1 : ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) = ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) * ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1))`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_prod_erase I (fun i => u + ρ i) hl, ← Finset.mul_prod_erase I (fun i => u + (ρ i + 1)) hl]`. Establish `a0` using `h0 l hl`. Establish `a1` using `h1 l hl`. Establish `a2 : u + (ρ l + 1) = u + ρ l + 1` using `by ring`. Rewrite using `[a2]`.

Clear the denominators using the available nonvanishing facts. Establish `s2 : ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) = (∏ i ∈ I, (u + ρ i)) * ∑ l ∈ I, (N l - Nd l) / (u + ρ l)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase I (fun i => u + ρ i) hl]`.

Establish `a0` using `h0 l hl`. Clear the denominators using the available nonvanishing facts. Establish `s3 : ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) = ∑ l ∈ I, (N l - Nd l) / (u + ρ l) - ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1))`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations.

Establish `a0` using `h0 l hl`. Establish `a1` using `h1 l hl`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e1` using `h.eval u`.

Rewrite `e1` using `[s1, hw u, s2]`. Rewrite using `[div_eq_iff (mul_ne_zero hx0 hx1), s3]`. Take the linear combination `-e1`.
-/
theorem absH {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (Qf : ℂ → ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * Qf u + ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0) :
    q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) =
      Qf u + ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) := by
  have hx0 : ∏ i ∈ I, (u + ρ i) ≠ 0 := Finset.prod_ne_zero_iff.2 h0
  have hx1 : ∏ i ∈ I, (u + (ρ i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact h1 i hi)
  have s1 : ∑ l ∈ I, N l * ((∏ j ∈ I.erase l, (u + ρ j)) * ∏ j ∈ I.erase l, (u + (ρ j + 1))) =
      ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) * ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.mul_prod_erase I (fun i => u + ρ i) hl, ← Finset.mul_prod_erase I (fun i => u + (ρ i + 1)) hl]
    have a0 := h0 l hl
    have a1 := h1 l hl
    have a2 : u + (ρ l + 1) = u + ρ l + 1 := by ring
    rw [a2]
    field_simp
  have s2 : ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j) =
      (∏ i ∈ I, (u + ρ i)) * ∑ l ∈ I, (N l - Nd l) / (u + ρ l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [← Finset.mul_prod_erase I (fun i => u + ρ i) hl]
    have a0 := h0 l hl
    field_simp
  have s3 : ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) =
      ∑ l ∈ I, (N l - Nd l) / (u + ρ l) - ∑ l ∈ I, N l / ((u + ρ l) * (u + ρ l + 1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have a0 := h0 l hl
    have a1 := h1 l hl
    field_simp
    ring
  have e1 := h.eval u
  rw [s1, hw u, s2] at e1
  rw [div_eq_iff (mul_ne_zero hx0 hx1), s3]
  linear_combination -e1

/- English proof (translation)
Rewrite using `[absH Nd h (fun u => c * (u ^ 2 + s * u) + c0) hw u h0 h1, absH Nd h (fun u => c * (u ^ 2 + s * u) + c0) hw v k0 k1]`. Establish `s4 : (u - v) * ∑ j ∈ I, (N j / ((u + ρ j + 1) * (v + ρ j + 1)) - Nd j / ((u + ρ j) * (v + ρ j))) = ∑ l ∈ I, (N l / (v + ρ l + 1) - Nd l / (v + ρ l)) - ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l))`. Rewrite using `[Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Establish `a0` using `h0 l hl`.

Establish `a1` using `h1 l hl`. Establish `b0` using `k0 l hl`. Establish `b1` using `k1 l hl`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Take the linear combination `s4`.
-/
theorem weighted_sum_difference_identity {I : Finset ℕ} {ρ : ℕ → ℂ} {q w : ℂ[X]} {N : ℕ → ℂ} (Nd : ℕ → ℂ) (h : W1 I ρ q w N) (c s c0 : ℂ)
    (hw : ∀ u, w.eval u = (∏ i ∈ I, (u + ρ i)) * (c * (u ^ 2 + s * u) + c0) +
      ∑ l ∈ I, (N l - Nd l) * ∏ j ∈ I.erase l, (u + ρ j))
    (u v : ℂ) (h0 : ∀ i ∈ I, u + ρ i ≠ 0) (h1 : ∀ i ∈ I, u + ρ i + 1 ≠ 0)
    (k0 : ∀ i ∈ I, v + ρ i ≠ 0) (k1 : ∀ i ∈ I, v + ρ i + 1 ≠ 0) :
    (u - v) * ((u + v + s) * (-c) + ∑ j ∈ I, (N j / ((u + ρ j + 1) * (v + ρ j + 1)) - Nd j / ((u + ρ j) * (v + ρ j)))) =
      q.eval v / ((∏ i ∈ I, (v + ρ i)) * ∏ i ∈ I, (v + (ρ i + 1))) -
      q.eval u / ((∏ i ∈ I, (u + ρ i)) * ∏ i ∈ I, (u + (ρ i + 1))) := by
  rw [absH Nd h (fun u => c * (u ^ 2 + s * u) + c0) hw u h0 h1, absH Nd h (fun u => c * (u ^ 2 + s * u) + c0) hw v k0 k1]
  have s4 : (u - v) * ∑ j ∈ I, (N j / ((u + ρ j + 1) * (v + ρ j + 1)) - Nd j / ((u + ρ j) * (v + ρ j))) =
      ∑ l ∈ I, (N l / (v + ρ l + 1) - Nd l / (v + ρ l)) - ∑ l ∈ I, (N l / (u + ρ l + 1) - Nd l / (u + ρ l)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l hl => ?_
    have a0 := h0 l hl
    have a1 := h1 l hl
    have b0 := k0 l hl
    have b1 := k1 l hl
    field_simp
    ring
  linear_combination s4

def rc (P : Par) (π : Ty P) : ℕ → ℂ := fun i => (rho P π i : ℂ)

def q1P (P : Par) : ℂ[X] :=
  ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))

/- English proof (translation)
Introduce `i hi j hj h`. Establish `h2 : rho P π i = rho P π j`. Unfold `rc at h`. Conclude with `h` after adjusting the coercions. Assume the negation of the conclusion as `hij`.

Break down `lt_or_gt_of_ne hij with h' | h'` into its components or cases. Conclude with `absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h'))`. Conclude with `absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h'))`.
-/
theorem rc_inj (P : Par) (hP : P.OK) (π : Ty P) :
    ∀ i ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), rc P π i = rc P π j → i = j := by
  intro i hi j hj h
  have h2 : rho P π i = rho P π j := by
    unfold rc at h; exact_mod_cast h
  by_contra hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h'))
  · exact absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h'))

/- English proof (translation)
Use `Mx3.wExact P hP π` as an intermediate fact. Unfold `W1`. Rewrite using `[mul_comm]`. Conclude with `this.symm`.
-/
theorem weight_model_identity (P : Par) (hP : P.OK) (π : Ty P) :
    W1 (Icc 1 (P.k - 1)) (rc P π) (C (-((P.T : ℂ) * P.T')) * q1P P) (wNum P π /ₘ coordinatePolynomial P π)
      (fun l => ((Nrm P l π : ℝ) : ℂ)) := by
  have := Mx3.wExact P hP π
  unfold W1
  rw [mul_comm]
  exact this.symm

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))`.
-/
theorem q_polynomial_monic (P : Par) : (q1P P).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))

/- English proof (translation)
Unfold `q1P`. Rewrite using `[natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]`. Establish `: ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2`. Introduce `i _`. Rewrite using `[(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]`.

Rewrite using `[Finset.sum_congr rfl this]`. Use `hP.k_pos` as an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem natDegree_q1_polynomial (P : Par) (hP : P.OK) : (q1P P).natDegree = 2 * (Icc 1 (P.k - 1)).card + 2 := by
  unfold q1P
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  have : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := by
    intro i _
    rw [(monic_X_add_C _).natDegree_mul (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  rw [Finset.sum_congr rfl this]
  have := hP.k_pos
  simp
  omega

/- English proof (translation)
Unfold `q1P`. Rewrite using `[Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[(monic_X_add_C _).nextCoeff_mul (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]`.
-/
theorem q_polynomial_next_coeff (P : Par) :
    (q1P P).nextCoeff = ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) := by
  unfold q1P
  rw [Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(monic_X_add_C _).nextCoeff_mul (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]

/- English proof (translation)
Unfold `q1P qC`. Simplify using `only [eval_mul, eval_C, eval_prod, eval_add, eval_X]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl (fun i _ => by ring)`.
-/
theorem q_eval (P : Par) (u : ℂ) : (C (-((P.T : ℂ) * P.T')) * q1P P).eval u = qC P u := by
  unfold q1P qC
  simp only [eval_mul, eval_C, eval_prod, eval_add, eval_X]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)

/- English proof (translation)
Establish `hl'` using `Finset.mem_Icc.1 hl`. Distinguish the cases in `hdeg : ∃ j0 ∈ (Icc 1 (P.k - 1)).erase l, rho P π j0 + 1 = rho P π l`. Take `⟨j0, hj0, hρ⟩` from `hdeg`. Establish `hj0'` using `Finset.mem_erase.1 hj0`. Establish `hNd : NrmDown P l π = 0`.

Unfold `NrmDown`. Establish `hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) = 0` using `Finset.prod_eq_zero hj0 (by linarith)`. Rewrite using `[hz, zero_mul, div_zero]`. Establish `hN0 : Nrm P j0 π = 0`. Unfold `Nrm`.

Establish `hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase j0, (rho P π j - rho P π j0 - 1) = 0` using `Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun e => hj0'.1 e.symm, hl⟩) (by linarith)`. Rewrite using `[hz, mul_zero, div_zero]`. Establish `hI` using `Mx3.tyInterlaces P hP π`. Establish `hlt : l < j0`. Assume the negation of the conclusion as `hcon`.

Establish `: j0 < l` using `lt_of_le_of_ne (not_lt.1 hcon) hj0'.1`. Use `Mx3.rho_inj P hP π j0 l hj0'.2 hl this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `o` using `(Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.2 j0 hj0'.2 hlt`. Establish `b` using `hI l hl`.

Establish `hu : P.u (l + 1) = rho P π l - 1 / 2` using `by linarith [o.1, b.2.2.1]`. Establish `hu' : P.u' (l + 1) = rho P π l - 1 / 2` using `by linarith [o.2, b.2.2.2]`. Establish `hq : (X + C (rc P π l)) ^ 2 ∣ C (-((P.T : ℂ) * P.T')) * q1P P`. Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Establish `hm : l + 1 ∈ Icc 1 P.k` using `Finset.mem_Icc.2 ⟨by omega, by omega⟩`.

Establish `hd` using `Finset.dvd_prod_of_mem (fun i => ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))) : ℂ[X])) hm`. Establish `e1 : (1 / 2 + (P.u (l + 1) : ℂ)) = rc P π l` using `by rw [hu]; unfold rc; push_cast; ring`. Establish `e2 : (1 / 2 + (P.u' (l + 1) : ℂ)) = rc P π l` using `by rw [hu']; unfold rc; push_cast; ring`. Simplify using `only [e1, e2] at hd`. Rewrite using `[pow_two]`.

Conclude with `hd`. Use `rootB (weight_model_identity P hP π) (rc_inj P hP π) hl hj0'.2 hj0'.1 (by unfold rc; exact_mod_cast hρ) hq (by simp only [hN0]; simp)` as an intermediate fact. Rewrite using `[this, hNd]`. Simplify using the standard rewrite rules. Use `push Not at hdeg`.

Establish `hA1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j hj h0`. Conclude with `hdeg j hj (by linarith)`. Establish `hA0 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) ≠ 0`.

Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `j hj h0`. Establish `hj'` using `Finset.mem_erase.1 hj`. Apply `hj'.1` to reduce the goal to its premises. Apply `rc_inj P hP π j hj'.2 l hl` to reduce the goal to its premises.

Unfold `rc`. Establish `: rho P π j = rho P π l` using `by linarith`. Rewrite using `[this]`. Establish `hk : NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) * ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) = -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l)`. Unfold `NrmDown`.

Conclude with `div_mul_cancel₀ _ (mul_ne_zero hA1 hA0)`. Establish `hk'` using `congrArg (fun x : ℝ => (x : ℂ)) hk`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one] at hk'`. Establish `hA1c : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l + 1) ≠ 0`. Use `hA1` as an intermediate fact.

Unfold `rc`. Introduce `h0`. Apply `this` to reduce the goal to its premises. Conclude with `h0` after adjusting the coercions. Use `rootA (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) hl hA1c ?_` and prove the remaining obligations.

Rewrite using `[q_eval]`. Establish `hr` using `(Mx3.realPoints P π (-rho P π l)).2`. Establish `e : (((-rho P π l : ℝ)) : ℂ) = -(rc P π l)` using `by unfold rc; push_cast; ring`. Rewrite `hr` using `[e]`. Rewrite using `[hr]`.

Conclude with `hk'`.
-/
theorem model_root (P : Par) (hP : P.OK) (π : Ty P) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    (wNum P π /ₘ coordinatePolynomial P π).eval (-(rc P π l)) = (((Nrm P l π : ℝ) : ℂ) - ((NrmDown P l π : ℝ) : ℂ)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l) := by
  have hl' := Finset.mem_Icc.1 hl
  by_cases hdeg : ∃ j0 ∈ (Icc 1 (P.k - 1)).erase l, rho P π j0 + 1 = rho P π l
  · obtain ⟨j0, hj0, hρ⟩ := hdeg
    have hj0' := Finset.mem_erase.1 hj0
    have hNd : NrmDown P l π = 0 := by
      unfold NrmDown
      have hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) = 0 :=
        Finset.prod_eq_zero hj0 (by linarith)
      rw [hz, zero_mul, div_zero]
    have hN0 : Nrm P j0 π = 0 := by
      unfold Nrm
      have hz : ∏ j ∈ (Icc 1 (P.k - 1)).erase j0, (rho P π j - rho P π j0 - 1) = 0 :=
        Finset.prod_eq_zero (Finset.mem_erase.2 ⟨fun e => hj0'.1 e.symm, hl⟩) (by linarith)
      rw [hz, mul_zero, div_zero]
    have hI := Mx3.tyInterlaces P hP π
    have hlt : l < j0 := by
      by_contra hcon
      have : j0 < l := lt_of_le_of_ne (not_lt.1 hcon) hj0'.1
      have := Mx3.rho_inj P hP π j0 l hj0'.2 hl this
      linarith
    have o := (Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.2 j0 hj0'.2 hlt
    have b := hI l hl
    have hu : P.u (l + 1) = rho P π l - 1 / 2 := by linarith [o.1, b.2.2.1]
    have hu' : P.u' (l + 1) = rho P π l - 1 / 2 := by linarith [o.2, b.2.2.2]
    have hq : (X + C (rc P π l)) ^ 2 ∣ C (-((P.T : ℂ) * P.T')) * q1P P := by
      apply Dvd.dvd.mul_left
      have hm : l + 1 ∈ Icc 1 P.k := Finset.mem_Icc.2 ⟨by omega, by omega⟩
      have hd := Finset.dvd_prod_of_mem
        (fun i => ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))) : ℂ[X])) hm
      have e1 : (1 / 2 + (P.u (l + 1) : ℂ)) = rc P π l := by rw [hu]; unfold rc; push_cast; ring
      have e2 : (1 / 2 + (P.u' (l + 1) : ℂ)) = rc P π l := by rw [hu']; unfold rc; push_cast; ring
      simp only [e1, e2] at hd
      rw [pow_two]
      exact hd
    have := rootB (weight_model_identity P hP π) (rc_inj P hP π) hl hj0'.2 hj0'.1
      (by unfold rc; exact_mod_cast hρ) hq (by simp only [hN0]; simp)
    rw [this, hNd]; simp
  · push Not at hdeg
    have hA1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h0
      exact hdeg j hj (by linarith)
    have hA0 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro j hj h0
      have hj' := Finset.mem_erase.1 hj
      apply hj'.1
      apply rc_inj P hP π j hj'.2 l hl
      unfold rc
      have : rho P π j = rho P π l := by linarith
      rw [this]
    have hk : NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) = -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) := by
      unfold NrmDown
      exact div_mul_cancel₀ _ (mul_ne_zero hA1 hA0)
    have hk' := congrArg (fun x : ℝ => (x : ℂ)) hk
    simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_one] at hk'
    have hA1c : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rc P π j - rc P π l + 1) ≠ 0 := by
      have := hA1
      unfold rc
      intro h0
      apply this
      exact_mod_cast h0
    refine rootA (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) hl hA1c ?_
    rw [q_eval]
    have hr := (Mx3.realPoints P π (-rho P π l)).2
    have e : (((-rho P π l : ℝ)) : ℂ) = -(rc P π l) := by unfold rc; push_cast; ring
    rw [e] at hr
    rw [hr]
    exact hk'

/- English proof (translation)
Rewrite using `[q_polynomial_next_coeff]`. Establish `e1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) = ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) + (P.k : ℂ)`. Rewrite using `[Finset.sum_congr rfl (fun i _ => (by ring : (1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ)) = ((P.u i : ℂ) + P.u' i) + 1)), Finset.sum_add_distrib]`. Simplify using the standard rewrite rules. Establish `e2 : ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) = ∑ i ∈ Icc 1 (P.k - 1), rc P π i + ((P.k : ℂ) - 1)`.

Rewrite using `[Finset.sum_add_distrib]`. Simplify using `[Nat.cast_sub hP.k_pos]`. Rewrite using `[e1, e2]`. Unfold `aC rc`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem s_eq (P : Par) (hP : P.OK) (π : Ty P) :
    (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) - ∑ i ∈ Icc 1 (P.k - 1), rc P π i =
      1 + 2 * (aC P π : ℂ) := by
  rw [q_polynomial_next_coeff]
  have e1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) + (P.k : ℂ) := by
    rw [Finset.sum_congr rfl (fun i _ => (by ring : (1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ)) =
      ((P.u i : ℂ) + P.u' i) + 1)), Finset.sum_add_distrib]
    simp
  have e2 : ∑ i ∈ Icc 1 (P.k - 1), (rc P π i + 1) = ∑ i ∈ Icc 1 (P.k - 1), rc P π i + ((P.k : ℂ) - 1) := by
    rw [Finset.sum_add_distrib]
    simp [Nat.cast_sub hP.k_pos]
  rw [e1, e2]
  unfold aC rc
  push_cast
  ring

/- English proof (translation)
Introduce `i hi`. Use `hu π i hi 0 (by simp)` as an intermediate fact. Simplify `this` using `[rc]`.
-/
theorem good0 {P : Par} {u : ℂ} (hu : Good P u) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), u + rc P π i ≠ 0 := by
  intro i hi
  have := hu π i hi 0 (by simp)
  simpa [rc] using this

/- English proof (translation)
Introduce `i hi`. Use `hu π i hi 1 (by simp)` as an intermediate fact. Simplify `this` using `[rc]`.
-/
theorem good1 {P : Par} {u : ℂ} (hu : Good P u) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), u + rc P π i + 1 ≠ 0 := by
  intro i hi
  have := hu π i hi 1 (by simp)
  simpa [rc] using this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coordinate_product_eq (P : Par) (π : Ty P) (u : ℂ) : xC P π u = ∏ i ∈ Icc 1 (P.k - 1), (u + rc P π i) := rfl

/- English proof (translation)
Unfold `xC rc`. Conclude with `Finset.prod_congr rfl (fun i _ => by ring)`.
-/
theorem x_eval_shift_prod (P : Par) (π : Ty P) (u : ℂ) : xC P π (u + 1) = ∏ i ∈ Icc 1 (P.k - 1), (u + (rc P π i + 1)) := by
  unfold xC rc
  exact Finset.prod_congr rfl (fun i _ => by ring)

/- English proof (translation)
Establish `e1` using `(weight_model_identity P hP π).eval u`. Establish `hx1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rc P π i + 1)) ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact good1 hu π i hi)`. Rewrite `e1` using `[q_eval]`. Rewrite using `[x_eval_shift_prod]`. Use `show (wNum P π /ₘ coordinatePolynomial P π).eval u = _`.

Apply `mul_right_cancel₀ hx1` to reduce the goal to its premises. Rewrite using `[e1, add_mul, div_mul_cancel₀ _ hx1, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase (Icc 1 (P.k - 1)) (fun i => u + (rc P π i + 1)) hl]`.

Establish `a1` using `good1 hu π l hl`. Establish `a2 : u + (rc P π l + 1) = u + rc P π l + 1` using `by ring`. Establish `a3 : xEx P {l} π u = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (u + rc P π j)`. Unfold `xEx rc`. Rewrite using `[Finset.sdiff_singleton_eq_erase]`.

Establish `a4 : (rho P π l : ℂ) = rc P π l` using `rfl`. Rewrite using `[a2, a3, a4]`. Clear the denominators using the available nonvanishing facts.
-/
theorem wC_eq (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (hu : Good P u) :
    wC P π u = qC P u / xC P π (u + 1) +
      ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have e1 := (weight_model_identity P hP π).eval u
  have hx1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rc P π i + 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun i hi => by rw [← add_assoc]; exact good1 hu π i hi)
  rw [q_eval] at e1
  rw [x_eval_shift_prod]
  show (wNum P π /ₘ coordinatePolynomial P π).eval u = _
  apply mul_right_cancel₀ hx1
  rw [e1, add_mul, div_mul_cancel₀ _ hx1, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [← Finset.mul_prod_erase (Icc 1 (P.k - 1)) (fun i => u + (rc P π i + 1)) hl]
  have a1 := good1 hu π l hl
  have a2 : u + (rc P π l + 1) = u + rc P π l + 1 := by ring
  have a3 : xEx P {l} π u = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (u + rc P π j) := by
    unfold xEx rc
    rw [Finset.sdiff_singleton_eq_erase]
  have a4 : (rho P π l : ℂ) = rc P π l := rfl
  rw [a2, a3, a4]
  field_simp

/- English proof (translation)
Establish `hc : -((P.T : ℂ) * P.T') ≠ 0`. Establish `h1 : (P.T : ℂ) ≠ 0` using `by exact_mod_cast hP.T_pos.ne'`. Establish `h2 : (P.T' : ℂ) ≠ 0` using `by exact_mod_cast hP.T'_pos.ne'`. Conclude with `neg_ne_zero.2 (mul_ne_zero h1 h2)`. Take `⟨c0, hw⟩` from `quad (rc_inj P hP π) (q_polynomial_monic P) (natDegree_q1_polynomial P hP) hc (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) (model_root P hP π)`.

Rewrite `hw` using `[s_eq P hP π]`. Establish `h` using `weighted_sum_difference_identity (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) _ _ c0 hw u v (good0 hu π) (good1 hu π) (good0 hv π) (good1 hv π)`. Rewrite `h` using `[q_eval, q_eval, ← coordinate_product_eq, ← coordinate_product_eq, ← x_eval_shift_prod, ← x_eval_shift_prod]`. Rewrite using `[← h]`. Establish `hT : (P.TT : ℂ) = (P.T : ℂ) * P.T'` using `by unfold Par.TT; push_cast; ring`.

Rewrite using `[hT]`. Establish `: ∀ j, (rho P π j : ℂ) = rc P π j` using `fun _ => rfl`. Simplify using `only [this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scalar_partial_fraction_identity (P : Par) (hP : P.OK) (π : Ty P) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) * ((u + v + 1 + 2 * (aC P π : ℂ)) * (P.TT : ℂ) + ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))) =
      qC P v / (xC P π v * xC P π (v + 1)) - qC P u / (xC P π u * xC P π (u + 1)) := by
  have hc : -((P.T : ℂ) * P.T') ≠ 0 := by
    have h1 : (P.T : ℂ) ≠ 0 := by exact_mod_cast hP.T_pos.ne'
    have h2 : (P.T' : ℂ) ≠ 0 := by exact_mod_cast hP.T'_pos.ne'
    exact neg_ne_zero.2 (mul_ne_zero h1 h2)
  obtain ⟨c0, hw⟩ := quad (rc_inj P hP π) (q_polynomial_monic P) (natDegree_q1_polynomial P hP) hc
    (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) (model_root P hP π)
  rw [s_eq P hP π] at hw
  have h := weighted_sum_difference_identity (fun l => ((NrmDown P l π : ℝ) : ℂ)) (weight_model_identity P hP π) _ _ c0 hw u v
    (good0 hu π) (good1 hu π) (good0 hv π) (good1 hv π)
  rw [q_eval, q_eval, ← coordinate_product_eq, ← coordinate_product_eq, ← x_eval_shift_prod, ← x_eval_shift_prod] at h
  rw [← h]
  have hT : (P.TT : ℂ) = (P.T : ℂ) * P.T' := by unfold Par.TT; push_cast; ring
  rw [hT]
  have : ∀ j, (rho P π j : ℂ) = rc P π j := fun _ => rfl
  simp only [this]
  ring

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.WB

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.PC

open Matrix Finset Polynomial  Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

section Poly

variable {B : Type*} [Ring B] [Algebra ℂ B]

def ev (y : ℂ) : B[X] →+* B :=
  Polynomial.eval₂RingHom' (RingHom.id B) (algebraMap ℂ B y) fun a => (Algebra.commutes y a).symm

def IsPoly (f : ℂ → B) : Prop := ∃ p : B[X], ∀ y, f y = ev y p

def IsPolyS (a : ℂ → ℂ) : Prop := ∃ s : ℂ[X], ∀ y, a y = s.eval y

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_apply (y : ℂ) (p : B[X]) : ev y p = p.eval₂ (RingHom.id B) (algebraMap ℂ B y) := rfl

/- English proof (translation)
Rewrite using `[ev_apply, Polynomial.eval₂_C]`. Both sides reduce to the same expression.
-/
theorem ev_C (y : ℂ) (b : B) : ev y (C b) = b := by rw [ev_apply, Polynomial.eval₂_C]; rfl

/- English proof (translation)
Rewrite using `[ev_apply, Polynomial.eval₂_map, RingHom.id_comp]`. Conclude with `Polynomial.eval₂_at_apply (algebraMap ℂ B) y`.
-/
theorem ev_map (y : ℂ) (s : ℂ[X]) : ev y (s.map (algebraMap ℂ B)) = algebraMap ℂ B (s.eval y) := by
  rw [ev_apply, Polynomial.eval₂_map, RingHom.id_comp]
  exact Polynomial.eval₂_at_apply (algebraMap ℂ B) y

/- English proof (translation)
Assemble the required witnesses or components as `⟨C b, fun y => (ev_C y b).symm⟩`.
-/
theorem IsPoly.const (b : B) : IsPoly fun _ => b := ⟨C b, fun y => (ev_C y b).symm⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hf`. Take `⟨q, hq⟩` from `hg`. Conclude with `⟨p + q, fun y => by show f y + g y = _; rw [hp, hq, map_add]⟩`.
-/
theorem IsPoly.add {f g : ℂ → B} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun y => f y + g y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p + q, fun y => by show f y + g y = _; rw [hp, hq, map_add]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hf`. Take `⟨q, hq⟩` from `hg`. Conclude with `⟨p - q, fun y => by show f y - g y = _; rw [hp, hq, map_sub]⟩`.
-/
theorem IsPoly.sub {f g : ℂ → B} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun y => f y - g y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p - q, fun y => by show f y - g y = _; rw [hp, hq, map_sub]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hf`. Conclude with `⟨-p, fun y => by show -f y = _; rw [hp, map_neg]⟩`.
-/
theorem IsPoly.neg {f : ℂ → B} (hf : IsPoly f) : IsPoly fun y => -f y := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨-p, fun y => by show -f y = _; rw [hp, map_neg]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hf`. Take `⟨q, hq⟩` from `hg`. Conclude with `⟨p * q, fun y => by show f y * g y = _; rw [hp, hq, map_mul]⟩`.
-/
theorem IsPoly.mul {f g : ℂ → B} (hf : IsPoly f) (hg : IsPoly g) : IsPoly fun y => f y * g y := by
  obtain ⟨p, hp⟩ := hf; obtain ⟨q, hq⟩ := hg
  exact ⟨p * q, fun y => by show f y * g y = _; rw [hp, hq, map_mul]⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `ha`. Conclude with `⟨s.map (algebraMap ℂ B), fun y => by show algebraMap ℂ B (a y) = _; rw [hs, ev_map]⟩`.
-/
theorem IsPoly.algMap {a : ℂ → ℂ} (ha : IsPolyS a) : IsPoly fun y => algebraMap ℂ B (a y) := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨s.map (algebraMap ℂ B), fun y => by show algebraMap ℂ B (a y) = _; rw [hs, ev_map]⟩

/- English proof (translation)
Use `(IsPoly.algMap (B := B) ha).mul hf` as an intermediate fact. Simplify `this` using `only [Algebra.smul_def]`.
-/
theorem IsPoly.smul {a : ℂ → ℂ} {f : ℂ → B} (ha : IsPolyS a) (hf : IsPoly f) : IsPoly fun y => a y • f y := by
  have := (IsPoly.algMap (B := B) ha).mul hf
  simpa only [Algebra.smul_def] using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using IsPoly.const (0 : B)`. Consider the case `insert a s ha ih`. Establish `h1` using `(hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`. Use `(funext fun y => ?_ : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y) ▸ h1` and prove the remaining obligations.

Rewrite using `[Finset.sum_insert ha]`.
-/
theorem IsPoly.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → B} (hf : ∀ i ∈ s, IsPoly (f i)) :
    IsPoly fun y => ∑ i ∈ s, f i y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPoly.const (0 : B)
  | insert a s ha ih =>
    have h1 := (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine (funext fun y => ?_ : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y) ▸ h1
    rw [Finset.sum_insert ha]

/- English proof (translation)
Assemble the required witnesses or components as `⟨X, fun y => by simp⟩`.
-/
theorem IsPolyS.id : IsPolyS fun y => y := ⟨X, fun y => by simp⟩
/- English proof (translation)
Assemble the required witnesses or components as `⟨C c, fun y => by simp⟩`.
-/
theorem IsPolyS.const (c : ℂ) : IsPolyS fun _ => c := ⟨C c, fun y => by simp⟩
/- English proof (translation)
Take `⟨p, hp⟩` from `ha`. Take `⟨q, hq⟩` from `hb`. Conclude with `⟨p + q, fun y => by show a y + b y = _; rw [hp, hq, eval_add]⟩`.
-/
theorem IsPolyS.add {a b : ℂ → ℂ} (ha : IsPolyS a) (hb : IsPolyS b) : IsPolyS fun y => a y + b y := by
  obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
  exact ⟨p + q, fun y => by show a y + b y = _; rw [hp, hq, eval_add]⟩
/- English proof (translation)
Take `⟨p, hp⟩` from `ha`. Take `⟨q, hq⟩` from `hb`. Conclude with `⟨p - q, fun y => by show a y - b y = _; rw [hp, hq, eval_sub]⟩`.
-/
theorem IsPolyS.sub {a b : ℂ → ℂ} (ha : IsPolyS a) (hb : IsPolyS b) : IsPolyS fun y => a y - b y := by
  obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
  exact ⟨p - q, fun y => by show a y - b y = _; rw [hp, hq, eval_sub]⟩
/- English proof (translation)
Use `choose! p hp using ha`. Conclude with `⟨∏ i ∈ s, p i, fun y => by show ∏ i ∈ s, a i y = _; rw [eval_prod]; exact Finset.prod_congr rfl fun i hi => hp i hi y⟩`.
-/
theorem IsPolyS.prod {ι : Type*} (s : Finset ι) {a : ι → ℂ → ℂ} (ha : ∀ i ∈ s, IsPolyS (a i)) :
    IsPolyS fun y => ∏ i ∈ s, a i y := by
  classical
  choose! p hp using ha
  exact ⟨∏ i ∈ s, p i, fun y => by show ∏ i ∈ s, a i y = _; rw [eval_prod]; exact Finset.prod_congr rfl fun i hi => hp i hi y⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hf`. Use `⟨∑ n ∈ p.support, monomial n (φ (p.coeff n)), fun y => ?_⟩` and prove the remaining obligations. Use `show φ (f y) = _`. Rewrite using `[hp, ev_apply]`. Simplify using `only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, RingHom.id_apply, map_sum, eval_finsetSum, eval_monomial]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem IsPoly.dual {f : ℂ → B} (hf : IsPoly f) (φ : Module.Dual ℂ B) : IsPolyS fun y => φ (f y) := by
  obtain ⟨p, hp⟩ := hf
  refine ⟨∑ n ∈ p.support, monomial n (φ (p.coeff n)), fun y => ?_⟩
  show φ (f y) = _
  rw [hp, ev_apply]
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def, RingHom.id_apply,
    map_sum, eval_finsetSum, eval_monomial]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← map_pow, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `φ`. Take `⟨s, hs⟩` from `hf.dual φ`. Establish `h0 : s = 0`. Use `Polynomial.eq_zero_of_infinite_isRoot s (Set.Infinite.mono ?_ hS.infinite_compl)` and prove the remaining obligations.

Introduce `z hz`. Use `show s.eval z = 0`. Rewrite using `[← hs]`. Use `show φ (f z) = 0`. Rewrite using `[h z hz, map_zero]`.

Establish `h1 : φ (f y) = s.eval y` using `hs y`. Rewrite using `[h1, h0, eval_zero]`.
-/
theorem IsPoly.eq_zero {f : ℂ → B} (hf : IsPoly f) (S : Set ℂ) (hS : S.Finite) (h : ∀ y, y ∉ S → f y = 0) (y : ℂ) :
    f y = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨s, hs⟩ := hf.dual φ
  have h0 : s = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot s (Set.Infinite.mono ?_ hS.infinite_compl)
    intro z hz
    show s.eval z = 0
    rw [← hs]
    show φ (f z) = 0
    rw [h z hz, map_zero]
  have h1 : φ (f y) = s.eval y := hs y
  rw [h1, h0, eval_zero]

end Poly

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
Use `conv_lhs => rw [pi_eq_sum_univ' f]`. Simplify using `only [map_sum, map_smul]`.
-/
theorem kap_sum (f : Ty P → ℂ) : kap P D f = ∑ π, f π • kap P D (Pi.single π 1) := by
  conv_lhs => rw [pi_eq_sum_univ' f]
  simp only [map_sum, map_smul]

/- English proof (translation)
Establish `: (fun Y => kap P D fun π => F π Y) = fun Y => ∑ π, F π Y • kap P D (Pi.single π 1)`. Use function extensionality and compare the values at `Y`. Conclude with `kap_sum P D _`. Rewrite using `[this]`. Conclude with `IsPoly.sum _ fun π _ => IsPoly.smul (hF π) (IsPoly.const _)`.
-/
theorem isPoly_kap {F : Ty P → ℂ → ℂ} (hF : ∀ π, IsPolyS (F π)) : IsPoly fun Y => kap P D fun π => F π Y := by
  have : (fun Y => kap P D fun π => F π Y) = fun Y => ∑ π, F π Y • kap P D (Pi.single π 1) := by
    funext Y; exact kap_sum P D _
  rw [this]
  exact IsPoly.sum _ fun π _ => IsPoly.smul (hF π) (IsPoly.const _)

/- English proof (translation)
The claim follows from `IsPolyS.prod _ fun _ _ => IsPolyS.id.add (IsPolyS.const _)`.
-/
theorem isPolyS_xC (π : Ty P) : IsPolyS fun Y => xC P π Y :=
  IsPolyS.prod _ fun _ _ => IsPolyS.id.add (IsPolyS.const _)

/- English proof (translation)
The claim follows from `IsPolyS.prod _ fun _ _ => IsPolyS.id.add (IsPolyS.const _)`.
-/
theorem isPolyS_xEx (ex : Finset ℕ) (π : Ty P) : IsPolyS fun Y => xEx P ex π Y :=
  IsPolyS.prod _ fun _ _ => IsPolyS.id.add (IsPolyS.const _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, fun _ => rfl⟩`.
-/
theorem isPolyS_wC (π : Ty P) : IsPolyS fun Y => wC P π Y := ⟨_, fun _ => rfl⟩

/- English proof (translation)
The claim follows from `isPoly_kap P D (isPolyS_xC P)`.
-/
theorem isPoly_xA : IsPoly fun Y => xA P D Y := isPoly_kap P D (isPolyS_xC P)

/- English proof (translation)
The claim follows from `(IsPoly.const _).sub ((IsPoly.algMap (IsPolyS.id.add (IsPolyS.const _))).mul (IsPoly.const _))`.
-/
theorem isPoly_l0A : IsPoly fun Y => l0A P D Y :=
  (IsPoly.const _).sub ((IsPoly.algMap (IsPolyS.id.add (IsPolyS.const _))).mul (IsPoly.const _))

/- English proof (translation)
The claim follows from `(IsPoly.const _).sub ((IsPoly.algMap (IsPolyS.id.sub (IsPolyS.const _))).mul (IsPoly.const _))`.
-/
theorem isPoly_m0A : IsPoly fun Y => m0A P D Y :=
  (IsPoly.const _).sub ((IsPoly.algMap (IsPolyS.id.sub (IsPolyS.const _))).mul (IsPoly.const _))

/- English proof (translation)
The claim follows from `IsPoly.sum _ fun l _ => (IsPoly.const _).mul (isPoly_kap P D (isPolyS_xEx P {l}))`.
-/
theorem isPoly_S21 : IsPoly fun Y => weightedSumBis P D Y :=
  IsPoly.sum _ fun l _ => (IsPoly.const _).mul (isPoly_kap P D (isPolyS_xEx P {l}))

/- English proof (translation)
The claim follows from `IsPoly.sum _ fun l _ => (isPoly_kap P D (isPolyS_xEx P {l})).mul (IsPoly.const _)`.
-/
theorem isPoly_S12 : IsPoly fun Y => S12 P D Y :=
  IsPoly.sum _ fun l _ => (isPoly_kap P D (isPolyS_xEx P {l})).mul (IsPoly.const _)

/- English proof (translation)
The claim follows from `IsPoly.sum _ fun l _ => IsPoly.sum _ fun j _ => (IsPoly.const _).mul (isPoly_kap P D (isPolyS_xEx P {l, j}))`.
-/
theorem isPoly_quartic_sum : IsPoly fun Y => S4 P D Y :=
  IsPoly.sum _ fun l _ => IsPoly.sum _ fun j _ => (IsPoly.const _).mul (isPoly_kap P D (isPolyS_xEx P {l, j}))

/- English proof (translation)
The claim follows from `(IsPoly.const _).mul (isPoly_xA P D)`.
-/
theorem isPoly_diagonal_entry : IsPoly fun Y => t22 P D Y := (IsPoly.const _).mul (isPoly_xA P D)

/- English proof (translation)
The claim follows from `(((IsPoly.const _).mul (isPoly_xA P D)).mul (isPoly_l0A P D)).add (isPoly_S21 P D)`.
-/
theorem isPoly_t21 : IsPoly fun Y => t21 P D Y :=
  (((IsPoly.const _).mul (isPoly_xA P D)).mul (isPoly_l0A P D)).add (isPoly_S21 P D)

/- English proof (translation)
The claim follows from `(((IsPoly.const _).mul (isPoly_xA P D)).mul (isPoly_m0A P D)).add (isPoly_S12 P D)`.
-/
theorem isPoly_upper_right_entry : IsPoly fun Y => t12 P D Y :=
  (((IsPoly.const _).mul (isPoly_xA P D)).mul (isPoly_m0A P D)).add (isPoly_S12 P D)

/- English proof (translation)
The claim follows from `(((((IsPoly.const _).mul (isPoly_kap P D (isPolyS_wC P))).add ((((IsPoly.const _).mul (isPoly_xA P D)).mul (isPoly_m0A P D)).mul (isPoly_l0A P D))).add ((((IsPoly.const _).mul (isPoly_m0A P D)).mul (IsPoly.const _)).mul (isPoly_S21 P D))).add ((isPoly_S12 P D).mul (isPoly_l0A P D …`.
-/
theorem isPoly_upper_left_entry : IsPoly fun Y => t11 P D Y :=
  (((((IsPoly.const _).mul (isPoly_kap P D (isPolyS_wC P))).add
    ((((IsPoly.const _).mul (isPoly_xA P D)).mul (isPoly_m0A P D)).mul (isPoly_l0A P D))).add
    ((((IsPoly.const _).mul (isPoly_m0A P D)).mul (IsPoly.const _)).mul (isPoly_S21 P D))).add
    ((isPoly_S12 P D).mul (isPoly_l0A P D))).add ((IsPoly.const _).mul (isPoly_quartic_sum P D))

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j`. Apply the tactic sequence `exact isPoly_upper_left_entry P D`. Apply the tactic sequence `exact isPoly_upper_right_entry P D`. Conclude with `isPoly_t21 P D`. Apply the tactic sequence `exact isPoly_diagonal_entry P D`.
-/
theorem isPoly_QQr (i j : Fin 2) : IsPoly fun Y => QQr P D Y i j := by
  fin_cases i <;> fin_cases j
  · exact isPoly_upper_left_entry P D
  · exact isPoly_upper_right_entry P D
  · exact isPoly_t21 P D
  · exact isPoly_diagonal_entry P D

/- English proof (translation)
Use `Set.Finite.subset (Finset.finite_toSet ((Finset.univ : Finset (Ty P)).biUnion fun π => (Icc 1 (P.k - 1)).biUnion fun j => ({-2, -1, 0, 1, 2} : Finset ℤ).image fun n : ℤ => -(rho P π j : ℂ) - (n : ℂ))) ?_` and prove the remaining obligations. Introduce `Y hY`. Simplify using `only [Set.mem_ofPred_eq, Good, not_forall, not_not] at hY`. Take `⟨π, j, hj, n, hn, h⟩` from `hY`. Conclude with `Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨π, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_image.mpr ⟨n, hn, by linear_combination -h⟩⟩⟩)`.
-/
theorem bad_finite : {Y : ℂ | ¬ Good P Y}.Finite := by
  classical
  refine Set.Finite.subset (Finset.finite_toSet ((Finset.univ : Finset (Ty P)).biUnion fun π =>
    (Icc 1 (P.k - 1)).biUnion fun j => ({-2, -1, 0, 1, 2} : Finset ℤ).image fun n : ℤ => -(rho P π j : ℂ) - (n : ℂ))) ?_
  intro Y hY
  simp only [Set.mem_ofPred_eq, Good, not_forall, not_not] at hY
  obtain ⟨π, j, hj, n, hn, h⟩ := hY
  exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨π, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨j, hj,
    Finset.mem_image.mpr ⟨n, hn, by linear_combination -h⟩⟩⟩)

/- English proof (translation)
Use `set F : ℂ → ℂ → A P D := fun u v => (u - v) • (QQr P D u i j * QQr P D v k l - QQr P D v k l * QQr P D u i j) - (QQr P D u k j * QQr P D v i l - QQr P D v k j * QQr P D u i l) with hF`. Establish `hu : ∀ v, IsPoly fun u => F u v` using `fun v => (IsPoly.smul (IsPolyS.id.sub (IsPolyS.const v)) (((isPoly_QQr P D i j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P D i j)))).sub (((isPoly_QQr P D k j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P D i l)))`. Establish `hv : ∀ u, IsPoly fun v => F u v` using `fun u => (IsPoly.smul ((IsPolyS.const u).sub IsPolyS.id) (((IsPoly.const _).mul (isPoly_QQr P D k l)).sub ((isPoly_QQr P D k l).mul (IsPoly.const _)))).sub (((IsPoly.const _).mul (isPoly_QQr P D i l)).sub ((isPoly_QQr P D k j).mul (IsPoly.const _)))`. Establish `h1 : ∀ v, Good P v → ∀ u, F u v = 0`. Introduce `v gv`.

Use `(hu v).eq_zero ({Y : ℂ | ¬ Good P Y} ∪ {v, v + 1, v - 1}) ((bad_finite P).union (by simp)) ?_` and prove the remaining obligations. Introduce `u hu'`. Simplify using `only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_not] at hu'`. Take `⟨gu, a0, a1, a2⟩` from `hu'`. Conclude with `sub_eq_zero.mpr (h u v gu gv (fun e => a0 (by linear_combination e)) (fun e => a1 (by linear_combination e)) (fun e => a2 (by linear_combination e)) i j k l)`.

Establish `h2 : F u v = 0`. Use `(hv u).eq_zero {Y : ℂ | ¬ Good P Y} (bad_finite P) ?_ v` and prove the remaining obligations. Introduce `v' hv'`. Simplify using `only [Set.mem_ofPred_eq, not_not] at hv'`. Conclude with `h1 v' hv' u`.

Conclude with `sub_eq_zero.mp h2`.
-/
theorem entries_of_generic
    (h : ∀ u v : ℂ, Good P u → Good P v → u - v ≠ 0 → u - v ≠ 1 → u - v ≠ -1 → ∀ i j k l : Fin 2,
      (u - v) • (QQr P D u i j * QQr P D v k l - QQr P D v k l * QQr P D u i j) =
        QQr P D u k j * QQr P D v i l - QQr P D v k j * QQr P D u i l)
    (u v : ℂ) (i j k l : Fin 2) :
    (u - v) • (QQr P D u i j * QQr P D v k l - QQr P D v k l * QQr P D u i j) =
      QQr P D u k j * QQr P D v i l - QQr P D v k j * QQr P D u i l := by
  set F : ℂ → ℂ → A P D := fun u v => (u - v) • (QQr P D u i j * QQr P D v k l - QQr P D v k l * QQr P D u i j) -
    (QQr P D u k j * QQr P D v i l - QQr P D v k j * QQr P D u i l) with hF
  have hu : ∀ v, IsPoly fun u => F u v := fun v =>
    (IsPoly.smul (IsPolyS.id.sub (IsPolyS.const v))
      (((isPoly_QQr P D i j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P D i j)))).sub
      (((isPoly_QQr P D k j).mul (IsPoly.const _)).sub ((IsPoly.const _).mul (isPoly_QQr P D i l)))
  have hv : ∀ u, IsPoly fun v => F u v := fun u =>
    (IsPoly.smul ((IsPolyS.const u).sub IsPolyS.id)
      (((IsPoly.const _).mul (isPoly_QQr P D k l)).sub ((isPoly_QQr P D k l).mul (IsPoly.const _)))).sub
      (((IsPoly.const _).mul (isPoly_QQr P D i l)).sub ((isPoly_QQr P D k j).mul (IsPoly.const _)))
  have h1 : ∀ v, Good P v → ∀ u, F u v = 0 := by
    intro v gv
    refine (hu v).eq_zero ({Y : ℂ | ¬ Good P Y} ∪ {v, v + 1, v - 1})
      ((bad_finite P).union (by simp)) ?_
    intro u hu'
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, not_not] at hu'
    obtain ⟨gu, a0, a1, a2⟩ := hu'
    exact sub_eq_zero.mpr (h u v gu gv (fun e => a0 (by linear_combination e)) (fun e => a1 (by linear_combination e))
      (fun e => a2 (by linear_combination e)) i j k l)
  have h2 : F u v = 0 := by
    refine (hv u).eq_zero {Y : ℂ | ¬ Good P Y} (bad_finite P) ?_ v
    intro v' hv'
    simp only [Set.mem_ofPred_eq, not_not] at hv'
    exact h1 v' hv' u
  exact sub_eq_zero.mp h2

section Entries

variable {B : Type} [Ring B]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, E1, E2, Fintype.sum_prod_type]`.
-/
theorem kronecker_E1_E2_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E1 M * E2 N) (i, k) (j, l) = M i j * N k l := by
  simp [Matrix.mul_apply, E1, E2, Fintype.sum_prod_type]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, E1, E2, Fintype.sum_prod_type]`.
-/
theorem kronecker_embed_mul_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j := by
  simp [Matrix.mul_apply, E1, E2, Fintype.sum_prod_type]

/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]`.
-/
theorem Pf_mul_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]

/- English proof (translation)
Apply the tactic sequence `fin_cases j <;> fin_cases l <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]`.
-/
theorem mul_Pf_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) := by
  fin_cases j <;> fin_cases l <;> simp [Matrix.mul_apply, Pf, Fintype.sum_prod_type]

end Entries

/- English proof (translation)
Introduce `H P D _ hP Y Y'`. Apply `Matrix.ext` to reduce the goal to its premises. Introduce and unpack `⟨i, k⟩ ⟨j, l⟩`. Rewrite using `[Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply, kronecker_E1_E2_apply, kronecker_embed …`. Establish `h` using `H P D hP Y' Y i j k l`.

Rewrite `h` using `[smul_sub]`. Rewrite using `[sub_eq_sub_iff_sub_eq_sub]`. Conclude with `h`.
-/
theorem ofEntries : QQRTTOfEntries := by
  intro H P D _ hP Y Y'
  apply Matrix.ext
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply, kronecker_E1_E2_apply, kronecker_embed_mul_apply,
    kronecker_embed_mul_apply]
  have h := H P D hP Y' Y i j k l
  rw [smul_sub] at h
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact h

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.PC

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.L3

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
Unfold `lam`. Establish `e1 : kap P D f * (kap P D (rr P j v) * SS P D j) = kap P D (f * rr P j v) * SS P D j`. Rewrite using `[← mul_assoc, kap_mul]`. Establish `e2 : (kap P D (rr P j v) * SS P D j) * kap P D f = kap P D (rr P j v * f') * SS P D j`. Rewrite using `[mul_assoc, ← S_shift P D j f f' hs, ← mul_assoc, kap_mul]`.

Establish `e3 : kap P D f * (kap P D (rr P j u) * SS P D j - kap P D (rr P j v) * SS P D j) = kap P D (f * (rr P j u - rr P j v)) * SS P D j`. Rewrite using `[← sub_mul, ← map_sub, ← mul_assoc, kap_mul]`. Rewrite using `[e1, e2, e3, ← sub_mul, ← map_sub, ← smul_mul_assoc, ← smul_mul_assoc, ← map_smul, ← map_smul]`. Use `congr 2`. Use function extensionality and compare the values at `π`.

Simplify using `only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]`. Take the linear combination `hf π`.
-/
theorem comm_term (j : ℕ) (f f' : Ty P → ℂ) (hs : ∀ π π', Up P j π π' → f' π' = f π) (c u v : ℂ)
    (hf : ∀ π, (u - v) * ((f π - f' π) * rr P j v π) = c * (f π * (rr P j u π - rr P j v π))) :
    (u - v) • (kap P D f * lam P D j v - lam P D j v * kap P D f) = c • (kap P D f * (lam P D j u - lam P D j v)) := by
  unfold lam
  have e1 : kap P D f * (kap P D (rr P j v) * SS P D j) = kap P D (f * rr P j v) * SS P D j := by
    rw [← mul_assoc, kap_mul]
  have e2 : (kap P D (rr P j v) * SS P D j) * kap P D f = kap P D (rr P j v * f') * SS P D j := by
    rw [mul_assoc, ← S_shift P D j f f' hs, ← mul_assoc, kap_mul]
  have e3 : kap P D f * (kap P D (rr P j u) * SS P D j - kap P D (rr P j v) * SS P D j) =
      kap P D (f * (rr P j u - rr P j v)) * SS P D j := by
    rw [← sub_mul, ← map_sub, ← mul_assoc, kap_mul]
  rw [e1, e2, e3, ← sub_mul, ← map_sub, ← smul_mul_assoc, ← smul_mul_assoc, ← map_smul, ← map_smul]
  congr 2
  funext π
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  linear_combination hf π

/- English proof (translation)
Unfold `abelian₂`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun j hj => comm_term P D j f (f' j) (hs j hj) c u v (hf j hj)`.
-/
theorem comm_sum (f : Ty P → ℂ) (f' : ℕ → Ty P → ℂ) (c u v : ℂ)
    (hs : ∀ j ∈ Icc 1 (P.k - 1), ∀ π π', Up P j π π' → f' j π' = f π)
    (hf : ∀ j ∈ Icc 1 (P.k - 1), ∀ π,
      (u - v) * ((f π - f' j π) * rr P j v π) = c * (f π * (rr P j u π - rr P j v π))) :
    (u - v) • (kap P D f * abelian₂ P D v - abelian₂ P D v * kap P D f) = c • (kap P D f * (abelian₂ P D u - abelian₂ P D v)) := by
  unfold abelian₂
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j hj => comm_term P D j f (f' j) (hs j hj) c u v (hf j hj)

/- English proof (translation)
Establish `h` using `comm_sum P D (fun π => xC P π u) (fun j π => (u + (rho P π j : ℂ) - 1) * xEx P {j} π u) (-1) u v (fun j hj π π' hU => by`. Rewrite using `[xEx_up P hU {j} (Finset.mem_singleton_self j), rho_up P hU hj, if_pos rfl, xC_split P π u hj]`. Use the proof step `ring)`. Use the proof step `(fun j hj π => by`. Establish `h1` using `good0 P hu π hj`.

Establish `h2` using `good0 P hv π hj`. Simplify using `only [rr]`. Rewrite using `[xC_split P π u hj]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Rewrite `h` using `[neg_one_smul]`. Conclude with `h`.
-/
theorem Lam1 (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (xA P D u * abelian₂ P D v - abelian₂ P D v * xA P D u) = -(xA P D u * (abelian₂ P D u - abelian₂ P D v)) := by
  have h := comm_sum P D (fun π => xC P π u)
    (fun j π => (u + (rho P π j : ℂ) - 1) * xEx P {j} π u) (-1) u v
    (fun j hj π π' hU => by
      rw [xEx_up P hU {j} (Finset.mem_singleton_self j), rho_up P hU hj, if_pos rfl, xC_split P π u hj]
      ring)
    (fun j hj π => by
      have h1 := good0 P hu π hj
      have h2 := good0 P hv π hj
      simp only [rr]
      rw [xC_split P π u hj]
      field_simp
      ring)
  rw [neg_one_smul] at h
  exact h

/- English proof (translation)
Establish `h` using `comm_sum P D (fun π => (xC P π (u + 1))⁻¹) (fun j π => (u + (rho P π j : ℂ) + 1) * (u + (rho P π j : ℂ))⁻¹ * (xC P π (u + 1))⁻¹) 1 u v (fun j hj π π' hU => by`. Establish `h0` using `good0 P hu π' hj`. Establish `h1` using `good1 P hu π' hj`. Rewrite using `[xC_split P π' (u + 1) hj, xC_split P π (u + 1) hj, xEx_up P hU {j} (Finset.mem_singleton_self j), mul_inv, mul_inv]`. Rewrite `h0`, `h1`, the goal using `[rho_up P hU hj, if_pos rfl]`.

Generalize the expression as in `(xEx P {j} π (u + 1))⁻¹ = Ei`. Establish `h2 : u + 1 + ((rho P π j : ℂ) + 1) ≠ 0` using `by intro h; apply h1; rw [← h]; ring`. Establish `h3 : u + 1 + (rho P π j : ℂ) ≠ 0` using `by intro h; apply h0; rw [← h]; ring`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Use the proof step `(fun j hj π => by`. Establish `h1` using `good0 P hu π hj`. Establish `h2` using `good0 P hv π hj`. Simplify using `only [rr]`. Generalize the expression as in `(xC P π (u + 1))⁻¹ = Xi`.

Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`. Rewrite `h` using `[one_smul]`. Conclude with `h`.
-/
theorem Lam2 (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • ((kap P D fun π => (xC P π (u + 1))⁻¹) * abelian₂ P D v -
      abelian₂ P D v * (kap P D fun π => (xC P π (u + 1))⁻¹)) =
      (kap P D fun π => (xC P π (u + 1))⁻¹) * (abelian₂ P D u - abelian₂ P D v) := by
  have h := comm_sum P D (fun π => (xC P π (u + 1))⁻¹)
    (fun j π => (u + (rho P π j : ℂ) + 1) * (u + (rho P π j : ℂ))⁻¹ * (xC P π (u + 1))⁻¹) 1 u v
    (fun j hj π π' hU => by
      have h0 := good0 P hu π' hj
      have h1 := good1 P hu π' hj
      rw [xC_split P π' (u + 1) hj, xC_split P π (u + 1) hj,
        xEx_up P hU {j} (Finset.mem_singleton_self j), mul_inv, mul_inv]
      rw [rho_up P hU hj, if_pos rfl] at h0 h1 ⊢
      generalize (xEx P {j} π (u + 1))⁻¹ = Ei
      have h2 : u + 1 + ((rho P π j : ℂ) + 1) ≠ 0 := by intro h; apply h1; rw [← h]; ring
      have h3 : u + 1 + (rho P π j : ℂ) ≠ 0 := by intro h; apply h0; rw [← h]; ring
      field_simp
      ring)
    (fun j hj π => by
      have h1 := good0 P hu π hj
      have h2 := good0 P hv π hj
      simp only [rr]
      generalize (xC P π (u + 1))⁻¹ = Xi
      field_simp
      ring)
  rw [one_smul] at h
  exact h

def sh (i j : ℕ) (b : ℂ) : Ty P → ℂ := fun π => (b + (rho P π j : ℂ) - if j = i then 1 else 0)⁻¹

/- English proof (translation)
Establish `h` using `S_shift P D i (rr P j b) (sh P i j b) (fun π π' hU => by`. Simplify using `only [sh, rr]`. Rewrite using `[rho_up P hU hj]`. Use `congr 1`. Use the proof step `ring)`.

Unfold `lam`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lam_mul (i : ℕ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (a b : ℂ) :
    lam P D i a * lam P D j b = kap P D (rr P i a * sh P i j b) * (SS P D i * SS P D j) := by
  have h := S_shift P D i (rr P j b) (sh P i j b) (fun π π' hU => by
    simp only [sh, rr]
    rw [rho_up P hU hj]
    congr 1
    ring)
  unfold lam
  calc kap P D (rr P i a) * SS P D i * (kap P D (rr P j b) * SS P D j)
      = kap P D (rr P i a) * (SS P D i * kap P D (rr P j b)) * SS P D j := by simp only [mul_assoc]
    _ = kap P D (rr P i a) * (kap P D (sh P i j b) * SS P D i) * SS P D j := by rw [h]
    _ = _ := by rw [← kap_mul]; simp only [mul_assoc]

def ee (i j : ℕ) (u v : ℂ) : Ty P → ℂ :=
  (u - v) • (rr P i u * sh P i j v - rr P i v * sh P i j u) -
    (rr P i u * sh P i j u - rr P i u * sh P i j v - (rr P i v * sh P i j u - rr P i v * sh P i j v))

def FF (i j : ℕ) (u v : ℂ) : A P D :=
  (u - v) • (lam P D i u * lam P D j v - lam P D i v * lam P D j u) -
    (lam P D i u - lam P D i v) * (lam P D j u - lam P D j v)

/- English proof (translation)
Unfold `FF ee`. Simplify using `only [sub_mul, mul_sub, lam_mul P D _ hj, map_sub, map_smul, smul_mul_assoc]`. Normalize the expressions using the abelian group laws.
-/
theorem FF_eq (i : ℕ) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (u v : ℂ) :
    FF P D i j u v = kap P D (ee P i j u v) * (SS P D i * SS P D j) := by
  unfold FF ee
  simp only [sub_mul, mul_sub, lam_mul P D _ hj, map_sub, map_smul, smul_mul_assoc]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `π`. Establish `h1` using `good0 P hu π hi`. Establish `h2` using `good0 P hv π hi`. Establish `h3` using `goodm1 P hu π hi`. Establish `h4` using `goodm1 P hv π hi`.

Simplify using `only [ee, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply, if_true]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_diag {i : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P i i u v = 0 := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := goodm1 P hu π hi
  have h4 := goodm1 P hv π hi
  simp only [ee, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply, if_true]
  field_simp
  ring

def ccL (i j : ℕ) (u v : ℂ) : Ty P → ℂ := fun π =>
  -((u - v) ^ 2) * (rr P i u π * rr P i v π * rr P j u π * rr P j v π)

/- English proof (translation)
Use function extensionality and compare the values at `π`. Establish `h1` using `good0 P hu π hi`. Establish `h2` using `good0 P hv π hi`. Establish `h3` using `good0 P hu π hj`. Establish `h4` using `good0 P hv π hj`.

Simplify using `only [ee, ccL, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, if_neg hne, sub_zero]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_off_diagonal_first {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P i j u v = ccL P i j u v * fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1 := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := good0 P hu π hj
  have h4 := good0 P hv π hj
  simp only [ee, ccL, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, if_neg hne, sub_zero]
  field_simp
  ring

/- English proof (translation)
Use function extensionality and compare the values at `π`. Establish `h1` using `good0 P hu π hi`. Establish `h2` using `good0 P hv π hi`. Establish `h3` using `good0 P hu π hj`. Establish `h4` using `good0 P hv π hj`.

Simplify using `only [ee, ccL, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul, if_neg hne.symm, sub_zero]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ee_off_diagonal_second {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    ee P j i u v = -(ccL P i j u v * fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) := by
  funext π
  have h1 := good0 P hu π hi
  have h2 := good0 P hv π hi
  have h3 := good0 P hu π hj
  have h4 := good0 P hv π hj
  simp only [ee, ccL, sh, rr, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, smul_eq_mul,
    if_neg hne.symm, sub_zero]
  field_simp
  ring

/- English proof (translation)
Establish `h` using `hC P D hP i hi j hj hne`. Establish `a1` using `S_shift P D i (fun π => ((rho P π j - rho P π i - 1 : ℝ) : ℂ)) (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by`. Rewrite using `[rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]`. Use `push_cast`. Use the proof step `ring)`.

Establish `a2` using `S_shift P D j (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) (fun π π' hU => by`. Rewrite using `[rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]`. Use the proof step `ring)`. Establish `b1` using `S_shift P D j (fun π => ((rho P π j - rho P π i + 1 : ℝ) : ℂ)) (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by`. Rewrite using `[rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]`.

Use `push_cast`. Use the proof step `ring)`. Establish `b2` using `S_shift P D i (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) (fun π π' hU => by`. Rewrite using `[rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]`. Use the proof step `ring)`.

Rewrite using `[← mul_assoc, a2, mul_assoc, a1, ← mul_assoc, h, mul_assoc, ← b1, ← mul_assoc, ← b2, mul_assoc]`.
-/
theorem comm_tgt (hC : SSComm) (hP : P.OK) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) :
    (kap P D fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) * (SS P D j * SS P D i) =
      (kap P D fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) * (SS P D i * SS P D j) := by
  have h := hC P D hP i hi j hj hne
  have a1 := S_shift P D i (fun π => ((rho P π j - rho P π i - 1 : ℝ) : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]
      push_cast
      ring)
  have a2 := S_shift P D j (fun π => (rho P π j : ℂ) - (rho P π i : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) - 1) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]
      ring)
  have b1 := S_shift P D j (fun π => ((rho P π j - rho P π i + 1 : ℝ) : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ)) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne.symm, if_pos rfl]
      push_cast
      ring)
  have b2 := S_shift P D i (fun π => (rho P π j : ℂ) - (rho P π i : ℂ))
    (fun π => (rho P π j : ℂ) - (rho P π i : ℂ) + 1) (fun π π' hU => by
      rw [rho_up P hU hj, rho_up P hU hi, if_neg hne, if_pos rfl]
      ring)
  rw [← mul_assoc, a2, mul_assoc, a1, ← mul_assoc, h, mul_assoc, ← b1, ← mul_assoc, ← b2, mul_assoc]

/- English proof (translation)
Distinguish the cases in `hne : j = i`. Substitute `hne` using the available equality. Rewrite using `[FF_eq P D _ hj, ee_diag P hj u v hu hv, map_zero, zero_mul, add_zero]`. Rewrite using `[FF_eq P D _ hj, FF_eq P D _ hi, ee_off_diagonal_first P hi hj hne u v hu hv, ee_off_diagonal_second P hi hj hne u v hu hv, map_neg, ← kap_mul, ← kap_mul, neg_mul, mul_assoc, mul_assoc, comm_tgt P D hC hP hi hj hne, add_neg_cancel]`.
-/
theorem FF_pair (hC : SSComm) (hP : P.OK) {i j : ℕ} (hi : i ∈ Icc 1 (P.k - 1))
    (hj : j ∈ Icc 1 (P.k - 1)) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    FF P D i j u v + FF P D j i u v = 0 := by
  by_cases hne : j = i
  · subst hne
    rw [FF_eq P D _ hj, ee_diag P hj u v hu hv, map_zero, zero_mul, add_zero]
  · rw [FF_eq P D _ hj, FF_eq P D _ hi, ee_off_diagonal_first P hi hj hne u v hu hv, ee_off_diagonal_second P hi hj hne u v hu hv,
      map_neg, ← kap_mul, ← kap_mul, neg_mul, mul_assoc, mul_assoc, comm_tgt P D hC hP hi hj hne,
      add_neg_cancel]

/- English proof (translation)
Establish `h1 : ∑ i ∈ I, ∑ j ∈ I, F i j + ∑ i ∈ I, ∑ j ∈ I, F i j = 0` using `by nth_rewrite 2 [Finset.sum_comm]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun j hj => h i hi j hj`.

Establish `h2 : (2 : ℂ) • ∑ i ∈ I, ∑ j ∈ I, F i j = 0` using `by rw [two_smul]; exact h1`. Conclude with `(smul_eq_zero.1 h2).resolve_left two_ne_zero`.
-/
theorem sum_antisymm {M : Type*} [AddCommGroup M] [Module ℂ M] (I : Finset ℕ) (F : ℕ → ℕ → M)
    (h : ∀ i ∈ I, ∀ j ∈ I, F i j + F j i = 0) : ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by
  have h1 : ∑ i ∈ I, ∑ j ∈ I, F i j + ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j hj => h i hi j hj
  have h2 : (2 : ℂ) • ∑ i ∈ I, ∑ j ∈ I, F i j = 0 := by rw [two_smul]; exact h1
  exact (smul_eq_zero.1 h2).resolve_left two_ne_zero

/- English proof (translation)
Establish `h` using `sum_antisymm (Icc 1 (P.k - 1)) (fun i j => FF P D i j u v) (fun i hi j hj => FF_pair P D hC hP hi hj u v hu hv)`. Rewrite using `[← sub_eq_zero, ← h]`. Unfold `abelian₂ FF`. Simplify using `only [← Finset.sum_sub_distrib, Finset.sum_mul_sum, Finset.smul_sum]`.
-/
theorem Lam3 (hC : SSComm) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (abelian₂ P D u * abelian₂ P D v - abelian₂ P D v * abelian₂ P D u) = (abelian₂ P D u - abelian₂ P D v) * (abelian₂ P D u - abelian₂ P D v) := by
  have h := sum_antisymm (Icc 1 (P.k - 1)) (fun i j => FF P D i j u v)
    (fun i hi j hj => FF_pair P D hC hP hi hj u v hu hv)
  rw [← sub_eq_zero, ← h]
  unfold abelian₂ FF
  simp only [← Finset.sum_sub_distrib, Finset.sum_mul_sum, Finset.smul_sum]

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.L3

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.L4

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
Rewrite using `[← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `[Finset.sum_apply]`.
-/
theorem kap_sum' (s : Finset ℕ) (f : ℕ → Ty P → ℂ) :
    kap P D (fun π => ∑ l ∈ s, f l π) = ∑ l ∈ s, kap P D (f l) := by
  rw [← map_sum]
  congr 1
  funext π
  simp [Finset.sum_apply]

def rr1 (j : ℕ) (u : ℂ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ) + 1)⁻¹

/- English proof (translation)
Unfold `rr rr1`. Rewrite using `[rho_up P h hj, if_pos rfl, add_assoc]`.
-/
theorem rr_up_same {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) {π π' : Ty P} (h : Up P j π π') (u : ℂ) :
    rr P j u π' = rr1 P j u π := by
  unfold rr rr1
  rw [rho_up P h hj, if_pos rfl, add_assoc]

/- English proof (translation)
Unfold `rr`. Rewrite using `[rho_up P h hj, if_neg hne, add_zero]`.
-/
theorem rr_up_ne {i j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) {π π' : Ty P} (h : Up P i π π') (u : ℂ) :
    rr P j u π' = rr P j u π := by
  unfold rr
  rw [rho_up P h hj, if_neg hne, add_zero]

/- English proof (translation)
Unfold `rr1`. Rewrite using `[rho_up P h hj, if_neg hne, add_zero]`.
-/
theorem rho_unchanged_off_index {i j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ i) {π π' : Ty P} (h : Up P i π π') (u : ℂ) :
    rr1 P j u π' = rr1 P j u π := by
  unfold rr1
  rw [rho_up P h hj, if_neg hne, add_zero]

/- English proof (translation)
Unfold `rr`. Rewrite using `[xC_split P π u hj]`. Clear denominators, using `[good0 P hu π hj]` for the nonvanishing conditions.
-/
theorem xC_rr {u : ℂ} (hu : Good P u) {j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    xC P π u * rr P j u π = xEx P {j} π u := by
  unfold rr
  rw [xC_split P π u hj]
  field_simp [good0 P hu π hj]

/- English proof (translation)
Unfold `rr`. Rewrite using `[xEx_split P π u hj hne]`. Clear denominators, using `[good0 P hu π hj]` for the nonvanishing conditions.
-/
theorem xEx_rr {u : ℂ} (hu : Good P u) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ l) (π : Ty P) :
    xEx P {l} π u * rr P j u π = xEx P {l, j} π u := by
  unfold rr
  rw [xEx_split P π u hj hne]
  field_simp [good0 P hu π hj]

/- English proof (translation)
Unfold `abelian₂ weightedSumBis lam xA`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, kap_mul]`. Use `S_shift P D j _ _ fun π π' h => ?_` and prove the remaining obligations.

Use `show xC P π' u * rr P j u π' = xEx P {j} π u`. Rewrite using `[xC_rr P hu hj, xEx_up P h {j} (by simp)]`.
-/
theorem xLam {u : ℂ} (hu : Good P u) : xA P D u * abelian₂ P D u = weightedSumBis P D u := by
  unfold abelian₂ weightedSumBis lam xA
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, kap_mul]
  refine S_shift P D j _ _ fun π π' h => ?_
  show xC P π' u * rr P j u π' = xEx P {j} π u
  rw [xC_rr P hu hj, xEx_up P h {j} (by simp)]

/- English proof (translation)
Unfold `Lams S12 lams xA`. Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, kap_mul]`. Use `Ss_shift P D j _ _ fun π π' h => ?_` and prove the remaining obligations.

Use `show rr P j u π' * xC P π' u = xEx P {j} π u`. Rewrite using `[mul_comm, xC_rr P hu hj, xEx_up P h {j} (by simp)]`.
-/
theorem Lamsx {u : ℂ} (hu : Good P u) : Lams P D u * xA P D u = S12 P D u := by
  unfold Lams S12 lams xA
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [mul_assoc, kap_mul]
  refine Ss_shift P D j _ _ fun π π' h => ?_
  show rr P j u π' * xC P π' u = xEx P {j} π u
  rw [mul_comm, xC_rr P hu hj, xEx_up P h {j} (by simp)]

/- English proof (translation)
The claim follows from `(Ss_shift P D l (fun π => xEx P {l} π u) (fun π => xEx P {l} π u) fun _ _ h => xEx_up P h {l} (Finset.mem_singleton_self l) u).symm`.
-/
theorem E_Ss (l : ℕ) (u : ℂ) :
    (kap P D fun π => xEx P {l} π u) * star (SS P D l) = star (SS P D l) * kap P D fun π => xEx P {l} π u :=
  (Ss_shift P D l (fun π => xEx P {l} π u) (fun π => xEx P {l} π u)
    fun _ _ h => xEx_up P h {l} (Finset.mem_singleton_self l) u).symm

/- English proof (translation)
Establish `h1 : kap P D ((fun π => xEx P {l} π u) * rr P j u) * SS P D j = SS P D j * kap P D fun π => xEx P {l, j} π u` using `S_shift P D j (fun π => xEx P {l, j} π u) ((fun π => xEx P {l} π u) * rr P j u) fun π π' h => by`. Rewrite using `[Pi.mul_apply, xEx_rr P hu hj hne, xEx_up P h {l, j} (by simp)]`. Rewrite using `[E_Ss, mul_assoc, ← mul_assoc (kap P D _) (kap P D _), kap_mul, h1, mul_assoc]`.
-/
theorem T_ne {u : ℂ} (hu : Good P u) {l j : ℕ} (hj : j ∈ Icc 1 (P.k - 1)) (hne : j ≠ l) :
    (kap P D fun π => xEx P {l} π u) * star (SS P D l) * (kap P D (rr P j u) * SS P D j) =
      star (SS P D l) * SS P D j * kap P D fun π => xEx P {l, j} π u := by
  have h1 : kap P D ((fun π => xEx P {l} π u) * rr P j u) * SS P D j = SS P D j * kap P D fun π => xEx P {l, j} π u :=
    S_shift P D j (fun π => xEx P {l, j} π u) ((fun π => xEx P {l} π u) * rr P j u) fun π π' h => by
      rw [Pi.mul_apply, xEx_rr P hu hj hne, xEx_up P h {l, j} (by simp)]
  rw [E_Ss, mul_assoc, ← mul_assoc (kap P D _) (kap P D _), kap_mul, h1, mul_assoc]

/- English proof (translation)
Establish `h1 : kap P D ((fun π => xEx P {l} π u) * rr P l u) * SS P D l = SS P D l * kap P D ((fun π => xEx P {l} π u) * rr1 P l u)` using `S_shift P D l ((fun π => xEx P {l} π u) * rr1 P l u) ((fun π => xEx P {l} π u) * rr P l u) fun π π' h => by`. Rewrite using `[Pi.mul_apply, Pi.mul_apply, xEx_up P h {l} (by simp), rr_up_same P hl h]`. Rewrite using `[E_Ss, mul_assoc, ← mul_assoc (kap P D _) (kap P D _), kap_mul, h1, ← mul_assoc, (hN P D hP l hl).1, kap_mul]`. Use `congr 1`. Use function extensionality and compare the values at `π`.

Simplify using `only [Pi.mul_apply, rr1]`. Rewrite using `[div_eq_mul_inv, mul_assoc]`.
-/
theorem T_eq (hP : P.OK) (hN : SSNorm) (u : ℂ) {l : ℕ} (hl : l ∈ Icc 1 (P.k - 1)) :
    (kap P D fun π => xEx P {l} π u) * star (SS P D l) * (kap P D (rr P l u) * SS P D l) =
      kap P D fun π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have h1 : kap P D ((fun π => xEx P {l} π u) * rr P l u) * SS P D l =
      SS P D l * kap P D ((fun π => xEx P {l} π u) * rr1 P l u) :=
    S_shift P D l ((fun π => xEx P {l} π u) * rr1 P l u) ((fun π => xEx P {l} π u) * rr P l u) fun π π' h => by
      rw [Pi.mul_apply, Pi.mul_apply, xEx_up P h {l} (by simp), rr_up_same P hl h]
  rw [E_Ss, mul_assoc, ← mul_assoc (kap P D _) (kap P D _), kap_mul, h1, ← mul_assoc, (hN P D hP l hl).1, kap_mul]
  congr 1
  funext π
  simp only [Pi.mul_apply, rr1]
  rw [div_eq_mul_inv, mul_assoc]

/- English proof (translation)
Establish `e1 : S12 P D u * abelian₂ P D u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => xEx P {l} π u) * star (SS P D l) * (kap P D (rr P j u) * SS P D j)` using `Finset.sum_mul_sum _ _ _ _`. Establish `e2 : ∀ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => xEx P {l} π u) * star (SS P D l) * (kap P D (rr P j u) * SS P D j) = (∑ j ∈ (Icc 1 (P.k - 1)).erase l, star (SS P D l) * SS P D j * kap P D fun π => xEx P {l, j} π u) + kap P D fun π => ((Nrm P l π : ℝ) : ℂ) * x …`. Introduce `l hl`. Rewrite using `[← Finset.sum_erase_add _ _ hl, T_eq P D hP hN u hl]`. Use `congrArg (· + _) ?_` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_erase.1 hj`. Conclude with `T_ne P D hu hj'.2 hj'.1`. Rewrite using `[e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib, kap_sum' P D _ (fun l π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1))]`. Both sides reduce to the same expression.
-/
theorem upper_sum_mul_lambda (hP : P.OK) {u : ℂ} (hu : Good P u) (hN : SSNorm) :
    S12 P D u * abelian₂ P D u = S4 P D u + kap P D fun π => ∑ l ∈ Icc 1 (P.k - 1),
      ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
  have e1 : S12 P D u * abelian₂ P D u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      (kap P D fun π => xEx P {l} π u) * star (SS P D l) * (kap P D (rr P j u) * SS P D j) :=
    Finset.sum_mul_sum _ _ _ _
  have e2 : ∀ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      (kap P D fun π => xEx P {l} π u) * star (SS P D l) * (kap P D (rr P j u) * SS P D j) =
      (∑ j ∈ (Icc 1 (P.k - 1)).erase l, star (SS P D l) * SS P D j * kap P D fun π => xEx P {l, j} π u) +
        kap P D fun π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
    intro l hl
    rw [← Finset.sum_erase_add _ _ hl, T_eq P D hP hN u hl]
    refine congrArg (· + _) ?_
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_erase.1 hj
    exact T_ne P D hu hj'.2 hj'.1
  rw [e1, Finset.sum_congr rfl e2, Finset.sum_add_distrib,
    kap_sum' P D _ (fun l π => ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1))]
  rfl

/- English proof (translation)
Rewrite using `[kap_sum' P D _ (fun j π => ((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) - ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))]`. Establish `e1 : Lams P D u * abelian₂ P D v = ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lams P D i u * lam P D j v` using `Finset.sum_mul_sum _ _ _ _`. Establish `e2 : abelian₂ P D v * Lams P D u = ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lam P D j v * lams P D i u`. Unfold `Lams abelian₂`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_comm]`.

Rewrite using `[e1, e2, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Establish `hlam : ∀ j ∈ Icc 1 (P.k - 1), lam P D j v = SS P D j * kap P D (rr1 P j v)` using `fun j hj => S_shift P D j _ _ fun π π' h => rr_up_same P hj h v`. Rewrite using `[Finset.sum_eq_single_of_mem i hi]`.

Establish `h1 : lams P D i u * lam P D i v = kap P D ((fun π => ((Nrm P i π : ℝ) : ℂ)) * (rr1 P i u * rr1 P i v))`. Unfold `lams lam`. Rewrite using `[mul_assoc, ← mul_assoc (kap P D _) (kap P D _), kap_mul, S_shift P D i (rr1 P i u * rr1 P i v) _ (fun π π' h => by show rr P i u π' * rr P i v π' = rr1 P i u π * rr1 P i v π`. Rewrite using `[rr_up_same P hi h, rr_up_same P hi h]),`. Use the proof step `← mul_assoc, (hN P D hP i hi).1, kap_mul]`.

Establish `h2 : lam P D i v * lams P D i u = kap P D (rr P i v * (fun π => ((NrmDown P i π : ℝ) : ℂ)) * rr P i u)`. Unfold `lams lam`. Rewrite using `[mul_assoc, ← mul_assoc (SS P D i), (hN P D hP i hi).2, kap_mul, kap_mul, mul_assoc]`. Rewrite using `[h1, h2, ← map_sub]`. Use `congr 1`.

Use function extensionality and compare the values at `π`. Simplify using `only [Pi.sub_apply, Pi.mul_apply, rr, rr1]`. Rewrite using `[div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j hj hne`.

Rewrite using `[sub_eq_zero, hlam j hj]`. Unfold `lams`. Establish `h3 : kap P D (rr P i u) * SS P D j = SS P D j * kap P D (rr P i u)` using `S_shift P D j _ _ fun π π' h => rr_up_ne P hi (Ne.symm hne) h u`. Establish `h4 : kap P D (rr1 P j v) * star (SS P D i) = star (SS P D i) * kap P D (rr1 P j v)` using `(Ss_shift P D i _ _ fun π π' h => rho_unchanged_off_index P hj hne h v).symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hM P D hP i hi j hj hne, kap_comm]`. Use `_ = SS P D j * (star (SS P D i) * kap P D (rr1 P j v)) * kap P D (rr P i u) := by simp only [mul_assoc]`. Use `_ = SS P D j * kap P D (rr1 P j v) * (star (SS P D i) * kap P D (rr P i u)) := by rw [← h4]; simp only [mul_assoc]`.
-/
theorem Lam4 (hP : P.OK) (u v : ℂ) (hN : SSNorm) (hM : SSMixed) :
    Lams P D u * abelian₂ P D v - abelian₂ P D v * Lams P D u = kap P D fun π => ∑ j ∈ Icc 1 (P.k - 1),
      (((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ)))) := by
  rw [kap_sum' P D _ (fun j π => ((Nrm P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ) + 1) * (v + (rho P π j : ℂ) + 1)) -
        ((NrmDown P j π : ℝ) : ℂ) / ((u + (rho P π j : ℂ)) * (v + (rho P π j : ℂ))))]
  have e1 : Lams P D u * abelian₂ P D v =
      ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lams P D i u * lam P D j v := Finset.sum_mul_sum _ _ _ _
  have e2 : abelian₂ P D v * Lams P D u =
      ∑ i ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), lam P D j v * lams P D i u := by
    unfold Lams abelian₂
    rw [Finset.sum_mul_sum, Finset.sum_comm]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.sum_sub_distrib]
  have hlam : ∀ j ∈ Icc 1 (P.k - 1), lam P D j v = SS P D j * kap P D (rr1 P j v) := fun j hj =>
    S_shift P D j _ _ fun π π' h => rr_up_same P hj h v
  rw [Finset.sum_eq_single_of_mem i hi]
  ·
    have h1 : lams P D i u * lam P D i v = kap P D ((fun π => ((Nrm P i π : ℝ) : ℂ)) * (rr1 P i u * rr1 P i v)) := by
      unfold lams lam
      rw [mul_assoc, ← mul_assoc (kap P D _) (kap P D _), kap_mul,
        S_shift P D i (rr1 P i u * rr1 P i v) _ (fun π π' h => by
          show rr P i u π' * rr P i v π' = rr1 P i u π * rr1 P i v π
          rw [rr_up_same P hi h, rr_up_same P hi h]),
        ← mul_assoc, (hN P D hP i hi).1, kap_mul]
    have h2 : lam P D i v * lams P D i u = kap P D (rr P i v * (fun π => ((NrmDown P i π : ℝ) : ℂ)) * rr P i u) := by
      unfold lams lam
      rw [mul_assoc, ← mul_assoc (SS P D i), (hN P D hP i hi).2, kap_mul, kap_mul, mul_assoc]
    rw [h1, h2, ← map_sub]
    congr 1
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply, rr, rr1]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv]
    ring
  · intro j hj hne
    rw [sub_eq_zero, hlam j hj]
    unfold lams
    have h3 : kap P D (rr P i u) * SS P D j = SS P D j * kap P D (rr P i u) :=
      S_shift P D j _ _ fun π π' h => rr_up_ne P hi (Ne.symm hne) h u
    have h4 : kap P D (rr1 P j v) * star (SS P D i) = star (SS P D i) * kap P D (rr1 P j v) :=
      (Ss_shift P D i _ _ fun π π' h => rho_unchanged_off_index P hj hne h v).symm
    calc star (SS P D i) * kap P D (rr P i u) * (SS P D j * kap P D (rr1 P j v))
        = star (SS P D i) * (kap P D (rr P i u) * SS P D j) * kap P D (rr1 P j v) := by simp only [mul_assoc]
      _ = star (SS P D i) * SS P D j * (kap P D (rr P i u) * kap P D (rr1 P j v)) := by rw [h3]; simp only [mul_assoc]
      _ = SS P D j * star (SS P D i) * (kap P D (rr1 P j v) * kap P D (rr P i u)) := by
          rw [hM P D hP i hi j hj hne, kap_comm]
      _ = SS P D j * (star (SS P D i) * kap P D (rr1 P j v)) * kap P D (rr P i u) := by simp only [mul_assoc]
      _ = SS P D j * kap P D (rr1 P j v) * (star (SS P D i) * kap P D (rr P i u)) := by rw [← h4]; simp only [mul_assoc]

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations.L4

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

section Abs
variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Simplify using `only [mul_assoc, lc hNw, hNG, mul_sub, lc hGw]`.
-/
theorem abs_Nc (N w G : B) (hNw : N * w = w * N) (hNG : N * G = G * N - w * G * G) (hGw : G * w = w * G) :
    N * (w * G) = (w * G) * N - (w * G) * (w * G) := by
  simp only [mul_assoc, lc hNw, hNG, mul_sub, lc hGw]

/- English proof (translation)
Establish `h : algebraMap ℂ B t = z * w - g` using `by rw [hg]; abel`. Rewrite using `[Algebra.smul_def, h]`. Simplify using `only [sub_mul, mul_assoc, lc1 hgG]`.
-/
theorem smul_GG_sq_identity (g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1) :
    t • (G * G) = z * (w * (G * G)) - G := by
  have h : algebraMap ℂ B t = z * w - g := by rw [hg]; abel
  rw [Algebra.smul_def, h]
  simp only [sub_mul, mul_assoc, lc1 hgG]

/- English proof (translation)
Rewrite using `[smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNsw]`. Simplify using `only [sub_mul, mul_assoc, hNsG, mul_add, one_mul, lc hwz]`. Normalize the expressions using the abelian group laws.
-/
theorem abs_Nsc (Ns g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1)
    (hNsw : Ns * w = w * Ns - 1) (hNsG : Ns * G = G * Ns + z * G * G) (hwz : w * z = z * w) :
    Ns * (w * G) = (w * G) * Ns + t • (G * G) := by
  rw [smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNsw]
  simp only [sub_mul, mul_assoc, hNsG, mul_add, one_mul, lc hwz]
  abel

/- English proof (translation)
Rewrite using `[smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNz]`. Simplify using `only [add_mul, mul_assoc, hNG, mul_sub, one_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem abs_Ncz (N g G z w : B) (t : ℂ) (hg : g = z * w - algebraMap ℂ B t) (hgG : g * G = 1)
    (hNz : N * z = z * N + 1) (hNG : N * G = G * N - w * G * G) :
    N * (z * G) = (z * G) * N - t • (G * G) := by
  rw [smul_GG_sq_identity g G z w t hg hgG, ← mul_assoc, hNz]
  simp only [add_mul, mul_assoc, hNG, mul_sub, one_mul]
  abel

end Abs

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

def cc : A P D := zbA P D * ggiA P D

def cz : A P D := zA P D * ggiA P D

/- English proof (translation)
Unfold `sc`. Conclude with `(map_mul _ _ _).symm`.
-/
theorem sc_mul (a b : D.Pr) : sc P D a * sc P D b = sc P D (a * b) := by
  unfold sc; exact (map_mul _ _ _).symm

/- English proof (translation)
The claim follows from `sc_mul P D _ _`.
-/
theorem cc_sc : cc P D = sc P D (D.zbP * D.ggiP P.TT) := sc_mul P D _ _
/- English proof (translation)
The claim follows from `sc_mul P D _ _`.
-/
theorem cz_sc : cz P D = sc P D (D.zP * D.ggiP P.TT) := sc_mul P D _ _

/- English proof (translation)
Unfold `l0A cc`. Rewrite using `[Algebra.smul_def]`.
-/
theorem lowering_constant_eq_shift (u : ℂ) : l0A P D u = -nabA P D - (u + 1 / 2) • cc P D := by
  unfold l0A cc; rw [Algebra.smul_def]

/- English proof (translation)
Unfold `m0A cz`. Rewrite using `[Algebra.smul_def]`.
-/
theorem raising_constant_eq_shift (u : ℂ) : m0A P D u = -nabsA P D - (u - 1 / 2) • cz P D := by
  unfold m0A cz; rw [Algebra.smul_def]

/- English proof (translation)
Unfold `lam`. Rewrite using `[mul_assoc, S_sc, ← mul_assoc, kap_sc, mul_assoc]`.
-/
theorem lam_sc (j : ℕ) (u : ℂ) (a : D.Pr) : lam P D j u * sc P D a = sc P D a * lam P D j u := by
  unfold lam; rw [mul_assoc, S_sc, ← mul_assoc, kap_sc, mul_assoc]

/- English proof (translation)
Unfold `abelian₂`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => lam_sc P D j u a`.
-/
theorem Lam_sc (u : ℂ) (a : D.Pr) : abelian₂ P D u * sc P D a = sc P D a * abelian₂ P D u := by
  unfold abelian₂; rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => lam_sc P D j u a

/- English proof (translation)
Unfold `lams`. Rewrite using `[mul_assoc, kap_sc, ← mul_assoc, Ss_sc, mul_assoc]`.
-/
theorem lams_sc (j : ℕ) (u : ℂ) (a : D.Pr) : lams P D j u * sc P D a = sc P D a * lams P D j u := by
  unfold lams; rw [mul_assoc, kap_sc, ← mul_assoc, Ss_sc, mul_assoc]

/- English proof (translation)
Unfold `Lams`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => lams_sc P D j u a`.
-/
theorem Lams_sc (u : ℂ) (a : D.Pr) : Lams P D u * sc P D a = sc P D a * Lams P D u := by
  unfold Lams; rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => lams_sc P D j u a

/- English proof (translation)
Simplify using `[fnsA]`.
-/
theorem zeta_mem_function_algebra : zA P D ∈ fnsA P D := by simp [fnsA]
/- English proof (translation)
Simplify using `[fnsA]`.
-/
theorem mem_zb : zbA P D ∈ fnsA P D := by simp [fnsA]
/- English proof (translation)
Simplify using `[fnsA]`.
-/
theorem mem_g : ggA P D ∈ fnsA P D := by simp [fnsA]
/- English proof (translation)
Simplify using `[fnsA]`.
-/
theorem mem_G : ggiA P D ∈ fnsA P D := by simp [fnsA]

/- English proof (translation)
The claim follows from `(levFns P D).1 x hx y hy`.
-/
theorem fcomm {x y : A P D} (hx : x ∈ fnsA P D) (hy : y ∈ fnsA P D) : x * y = y * x := (levFns P D).1 x hx y hy

/- English proof (translation)
The claim follows from `(levFns P D).2.2.2.2.2.2.1`.
-/
theorem gG : ggA P D * ggiA P D = 1 := (levFns P D).2.2.2.2.2.2.1
/- English proof (translation)
The claim follows from `(levFns P D).2.2.2.2.2.2.2.1`.
-/
theorem Gg : ggiA P D * ggA P D = 1 := (levFns P D).2.2.2.2.2.2.2.1
/- English proof (translation)
The claim follows from `(levFns P D).2.2.2.2.2.2.2.2`.
-/
theorem g_def : ggA P D = zA P D * zbA P D - algebraMap ℂ (A P D) (P.TT : ℂ) := (levFns P D).2.2.2.2.2.2.2.2

/- English proof (translation)
The claim follows from `(levNab P D).1`.
-/
theorem besselUnipotent_mulVec_middle_vec : nabA P D * zA P D = zA P D * nabA P D + 1 := (levNab P D).1
/- English proof (translation)
The claim follows from `(levNab P D).2.2.1`.
-/
theorem N_zb : nabA P D * zbA P D = zbA P D * nabA P D := (levNab P D).2.2.1
/- English proof (translation)
The claim follows from `(levNab P D).2.2.2.2.1`.
-/
theorem nabla_gamma_relations : nabA P D * ggA P D = ggA P D * nabA P D + zbA P D := (levNab P D).2.2.2.2.1
/- English proof (translation)
The claim follows from `(levNab P D).2.2.2.2.2.1`.
-/
theorem nabla_star_gamma_relations : nabA P D * ggiA P D = ggiA P D * nabA P D - zbA P D * ggiA P D * ggiA P D := (levNab P D).2.2.2.2.2.1
/- English proof (translation)
The claim follows from `(levNabs P D).1`.
-/
theorem Ns_zb : nabsA P D * zbA P D = zbA P D * nabsA P D - 1 := (levNabs P D).1
/- English proof (translation)
The claim follows from `(levNabs P D).2.2.1`.
-/
theorem nabla_star_commute_z : nabsA P D * zA P D = zA P D * nabsA P D := (levNabs P D).2.2.1
/- English proof (translation)
The claim follows from `(levNabs P D).2.2.2.2.1`.
-/
theorem nabla_star_mul_GG : nabsA P D * ggA P D = ggA P D * nabsA P D - zA P D := (levNabs P D).2.2.2.2.1
/- English proof (translation)
The claim follows from `(levNabs P D).2.2.2.2.2.1`.
-/
theorem nabla_star_gamma_inv_comm : nabsA P D * ggiA P D = ggiA P D * nabsA P D + zA P D * ggiA P D * ggiA P D := (levNabs P D).2.2.2.2.2.1

/- English proof (translation)
Unfold `cc`. Rewrite using `[lc (fcomm P D (mem_g P D) (mem_zb P D)), gG, mul_one]`.
-/
theorem g_cc : ggA P D * cc P D = zbA P D := by
  unfold cc; rw [lc (fcomm P D (mem_g P D) (mem_zb P D)), gG, mul_one]
/- English proof (translation)
Unfold `cz`. Rewrite using `[lc (fcomm P D (mem_g P D) (zeta_mem_function_algebra P D)), gG, mul_one]`.
-/
theorem g_cz : ggA P D * cz P D = zA P D := by
  unfold cz; rw [lc (fcomm P D (mem_g P D) (zeta_mem_function_algebra P D)), gG, mul_one]

/- English proof (translation)
Rewrite using `[g_cc, nabla_gamma_relations]`.
-/
theorem N_g : nabA P D * ggA P D = ggA P D * nabA P D + ggA P D * cc P D := by rw [g_cc, nabla_gamma_relations]
/- English proof (translation)
The claim follows from `nabla_star_gamma_relations P D`.
-/
theorem N_G : nabA P D * ggiA P D = ggiA P D * nabA P D - cc P D * ggiA P D := nabla_star_gamma_relations P D
/- English proof (translation)
Rewrite using `[g_cz, nabla_star_mul_GG]`.
-/
theorem Ns_g : nabsA P D * ggA P D = ggA P D * nabsA P D - ggA P D * cz P D := by rw [g_cz, nabla_star_mul_GG]
/- English proof (translation)
The claim follows from `nabla_star_gamma_inv_comm P D`.
-/
theorem Ns_G : nabsA P D * ggiA P D = ggiA P D * nabsA P D + cz P D * ggiA P D := nabla_star_gamma_inv_comm P D
/- English proof (translation)
The claim follows from `abs_Nc _ _ _ (N_zb P D) (nabla_star_gamma_relations P D) (fcomm P D (mem_G P D) (mem_zb P D))`.
-/
theorem N_cc : nabA P D * cc P D = cc P D * nabA P D - cc P D * cc P D :=
  abs_Nc _ _ _ (N_zb P D) (nabla_star_gamma_relations P D) (fcomm P D (mem_G P D) (mem_zb P D))
/- English proof (translation)
The claim follows from `abs_Nsc _ _ _ _ _ _ (g_def P D) (gG P D) (Ns_zb P D) (nabla_star_gamma_inv_comm P D) (fcomm P D (mem_zb P D) (zeta_mem_function_algebra P D))`.
-/
theorem Ns_cc : nabsA P D * cc P D = cc P D * nabsA P D + (P.TT : ℂ) • (ggiA P D * ggiA P D) :=
  abs_Nsc _ _ _ _ _ _ (g_def P D) (gG P D) (Ns_zb P D) (nabla_star_gamma_inv_comm P D) (fcomm P D (mem_zb P D) (zeta_mem_function_algebra P D))
/- English proof (translation)
The claim follows from `abs_Ncz _ _ _ _ _ _ (g_def P D) (gG P D) (besselUnipotent_mulVec_middle_vec P D) (nabla_star_gamma_relations P D)`.
-/
theorem N_cz : nabA P D * cz P D = cz P D * nabA P D - (P.TT : ℂ) • (ggiA P D * ggiA P D) :=
  abs_Ncz _ _ _ _ _ _ (g_def P D) (gG P D) (besselUnipotent_mulVec_middle_vec P D) (nabla_star_gamma_relations P D)

/- English proof (translation)
Unfold `cc`. Rewrite using `[lc (fcomm P D (mem_G P D) (mem_zb P D)), mul_assoc]`.
-/
theorem G_cc : ggiA P D * cc P D = cc P D * ggiA P D := by
  unfold cc; rw [lc (fcomm P D (mem_G P D) (mem_zb P D)), mul_assoc]
/- English proof (translation)
Unfold `cz`. Rewrite using `[lc (fcomm P D (mem_G P D) (zeta_mem_function_algebra P D)), mul_assoc]`.
-/
theorem G_cz : ggiA P D * cz P D = cz P D * ggiA P D := by
  unfold cz; rw [lc (fcomm P D (mem_G P D) (zeta_mem_function_algebra P D)), mul_assoc]
/- English proof (translation)
Unfold `cc`. Rewrite using `[mul_assoc, Gg, mul_one, lc (fcomm P D (mem_g P D) (mem_zb P D)), gG, mul_one]`.
-/
theorem cc_g : cc P D * ggA P D = ggA P D * cc P D := by
  unfold cc; rw [mul_assoc, Gg, mul_one, lc (fcomm P D (mem_g P D) (mem_zb P D)), gG, mul_one]
/- English proof (translation)
Unfold `cz`. Rewrite using `[mul_assoc, Gg, mul_one, lc (fcomm P D (mem_g P D) (zeta_mem_function_algebra P D)), gG, mul_one]`.
-/
theorem cz_g : cz P D * ggA P D = ggA P D * cz P D := by
  unfold cz; rw [mul_assoc, Gg, mul_one, lc (fcomm P D (mem_g P D) (zeta_mem_function_algebra P D)), gG, mul_one]
/- English proof (translation)
Rewrite using `[cc_sc, cz_sc, sc_mul, sc_mul]`. Use `congr 1`. Simplify using `only [DAlg.zP, DAlg.zbP, DAlg.ggiP]`. Rewrite using `[multiplierPair_mul D, multiplierPair_mul D]`. Conclude with `multiplierPair_comm D _ _ _ _`.
-/
theorem cz_cc : cz P D * cc P D = cc P D * cz P D := by
  rw [cc_sc, cz_sc, sc_mul, sc_mul]
  congr 1
  simp only [DAlg.zP, DAlg.zbP, DAlg.ggiP]
  rw [multiplierPair_mul D, multiplierPair_mul D]
  exact multiplierPair_comm D _ _ _ _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem g_sc : ggA P D = sc P D (D.ggP P.TT) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem G_sc : ggiA P D = sc P D (D.ggiP P.TT) := rfl

/- English proof (translation)
The claim follows from `(starGens P D).2.2.2.1`.
-/
theorem star_g : star (ggA P D) = ggA P D := (starGens P D).2.2.2.1
/- English proof (translation)
The claim follows from `(starGens P D).2.2.2.2.1`.
-/
theorem star_G : star (ggiA P D) = ggiA P D := (starGens P D).2.2.2.2.1
/- English proof (translation)
The claim follows from `(starGens P D).2.1`.
-/
theorem star_alt : star (zA P D) = zbA P D := (starGens P D).2.1
/- English proof (translation)
The claim follows from `(starGens P D).2.2.2.2.2`.
-/
theorem star_N : star (nabA P D) = nabsA P D := (starGens P D).2.2.2.2.2
/- English proof (translation)
Rewrite using `[← star_N, star_star]`.
-/
theorem star_Ns : star (nabsA P D) = nabA P D := by rw [← star_N, star_star]
/- English proof (translation)
Rewrite using `[← star_alt, star_star]`.
-/
theorem star_zb : star (zbA P D) = zA P D := by rw [← star_alt, star_star]
/- English proof (translation)
Unfold `cc cz`. Rewrite using `[star_mul, star_G, star_zb, fcomm P D (mem_G P D) (zeta_mem_function_algebra P D)]`.
-/
theorem star_cc : star (cc P D) = cz P D := by
  unfold cc cz; rw [star_mul, star_G, star_zb, fcomm P D (mem_G P D) (zeta_mem_function_algebra P D)]
/- English proof (translation)
Rewrite using `[← star_cc, star_star]`.
-/
theorem star_cz : star (cz P D) = cc P D := by rw [← star_cc, star_star]

/- English proof (translation)
Unfold `abelian₂`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Unfold `lam`. Rewrite using `[← mul_assoc, ← kap_nab, mul_assoc, (hS P D j hj).1, mul_sub, cc_sc, ← mul_assoc (sc P D _), ← kap_sc, ← cc_sc]`.

Simplify using `only [mul_assoc, cc]`.
-/
theorem N_Lam (hS : NabSS) (u : ℂ) : nabA P D * abelian₂ P D u = abelian₂ P D u * nabA P D - cc P D * abelian₂ P D u := by
  unfold abelian₂; rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold lam
  rw [← mul_assoc, ← kap_nab, mul_assoc, (hS P D j hj).1, mul_sub, cc_sc, ← mul_assoc (sc P D _), ← kap_sc, ← cc_sc]
  simp only [mul_assoc, cc]

/- English proof (translation)
Unfold `abelian₂`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Unfold `lam`. Rewrite using `[← mul_assoc, ← kap_nabs, mul_assoc, (hS P D j hj).2, mul_sub, cz_sc, ← mul_assoc (sc P D _), ← kap_sc, ← cz_sc]`.

Simplify using `only [mul_assoc, cz]`.
-/
theorem Ns_Lam (hS : NabSS) (u : ℂ) : nabsA P D * abelian₂ P D u = abelian₂ P D u * nabsA P D - cz P D * abelian₂ P D u := by
  unfold abelian₂; rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  unfold lam
  rw [← mul_assoc, ← kap_nabs, mul_assoc, (hS P D j hj).2, mul_sub, cz_sc, ← mul_assoc (sc P D _), ← kap_sc, ← cz_sc]
  simp only [mul_assoc, cz]

/- English proof (translation)
Establish `h` using `congrArg star (Ns_Lam P D hS (star u))`. Rewrite `h` using `[star_mul, star_sub, star_mul, star_mul, star_Lam, star_Ns, star_cz]`. Rewrite using `[h, cc_sc, Lams_sc]`. Normalize the expressions using the abelian group laws.
-/
theorem N_Lams (hS : NabSS) (u : ℂ) : nabA P D * Lams P D u = Lams P D u * nabA P D + cc P D * Lams P D u := by
  have h := congrArg star (Ns_Lam P D hS (star u))
  rw [star_mul, star_sub, star_mul, star_mul, star_Lam, star_Ns, star_cz] at h
  rw [h, cc_sc, Lams_sc]; abel

/- English proof (translation)
Establish `h` using `congrArg star (N_Lam P D hS (star u))`. Rewrite `h` using `[star_mul, star_sub, star_mul, star_mul, star_Lam, star_N, star_cc]`. Rewrite using `[h, cz_sc, Lams_sc]`. Normalize the expressions using the abelian group laws.
-/
theorem Ns_Lams (hS : NabSS) (u : ℂ) : nabsA P D * Lams P D u = Lams P D u * nabsA P D + cz P D * Lams P D u := by
  have h := congrArg star (N_Lam P D hS (star u))
  rw [star_mul, star_sub, star_mul, star_mul, star_Lam, star_N, star_cc] at h
  rw [h, cz_sc, Lams_sc]; abel

/- English proof (translation)
Unfold `mt`. Rewrite using `[lA_eq, lowering_constant_eq_shift, star_add, star_sub, star_neg, star_N, star_smul, star_cc, star_mul, star_Lam, star_G, G_sc, Lams_sc]`. Use `congr 3`. Simplify using the standard rewrite rules.
-/
theorem mt_eq (u : ℂ) : mt P D u = -nabsA P D - (u + 1 / 2) • cz P D + ggiA P D * Lams P D u := by
  unfold mt
  rw [lA_eq, lowering_constant_eq_shift, star_add, star_sub, star_neg, star_N, star_smul, star_cc, star_mul, star_Lam, star_G, G_sc, Lams_sc]
  congr 3
  simp

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

section Abs2
variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Simplify using `only [mul_assoc, lc h1, lc h2, lc1 hgG, lc1 hGg, lc h1g, lc h2g]`.
-/
theorem absSand (g G K1 K2 K3 : B) (hgG : g * G = 1) (hGg : G * g = 1)
    (h1 : K1 * G = G * K1) (h2 : K2 * G = G * K2) (h1g : K1 * g = g * K1) (h2g : K2 * g = g * K2) :
    g * K1 * (K2 * (G * G)) * (g * K3) = K1 * K2 * K3 := by
  simp only [mul_assoc, lc h1, lc h2, lc1 hgG, lc1 hGg, lc h1g, lc h2g]

/- English proof (translation)
Simplify using `only [mul_add, add_mul, mul_assoc, lc hXm, lc hXG, lc hSG]`. Normalize the expressions using the abelian group laws.
-/
theorem absN (g G X m0 l0 S12 L : B) (hXm : X * m0 = m0 * X) (hXG : X * G = G * X) (hSG : S12 * G = G * S12) :
    (g * X * m0 + S12) * (l0 + G * L) = g * X * m0 * l0 + g * m0 * G * (X * L) + S12 * l0 + G * (S12 * L) := by
  simp only [mul_add, add_mul, mul_assoc, lc hXm, lc hXG, lc hSG]
  abel

end Abs2

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
The claim follows from `(kap_nab P D _).symm`.
-/
theorem x_N (u : ℂ) : nabA P D * xA P D u = xA P D u * nabA P D := (kap_nab P D _).symm
/- English proof (translation)
The claim follows from `(kap_nabs P D _).symm`.
-/
theorem x_Ns (u : ℂ) : nabsA P D * xA P D u = xA P D u * nabsA P D := (kap_nabs P D _).symm
/- English proof (translation)
The claim follows from `kap_sc P D _ _`.
-/
theorem kap_g (f : Ty P → ℂ) : kap P D f * ggA P D = ggA P D * kap P D f := kap_sc P D _ _
/- English proof (translation)
The claim follows from `kap_sc P D _ _`.
-/
theorem kap_G (f : Ty P → ℂ) : kap P D f * ggiA P D = ggiA P D * kap P D f := kap_sc P D _ _
/- English proof (translation)
Rewrite using `[cc_sc]`. Conclude with `kap_sc P D _ _`.
-/
theorem kap_cc (f : Ty P → ℂ) : kap P D f * cc P D = cc P D * kap P D f := by rw [cc_sc]; exact kap_sc P D _ _
/- English proof (translation)
Rewrite using `[cz_sc]`. Conclude with `kap_sc P D _ _`.
-/
theorem kap_cz (f : Ty P → ℂ) : kap P D f * cz P D = cz P D * kap P D f := by rw [cz_sc]; exact kap_sc P D _ _
/- English proof (translation)
Rewrite using `[cc_sc]`. Conclude with `Lam_sc P D _ _`.
-/
theorem Lam_cc (u : ℂ) : abelian₂ P D u * cc P D = cc P D * abelian₂ P D u := by rw [cc_sc]; exact Lam_sc P D _ _
/- English proof (translation)
Rewrite using `[cz_sc]`. Conclude with `Lam_sc P D _ _`.
-/
theorem Lam_cz (u : ℂ) : abelian₂ P D u * cz P D = cz P D * abelian₂ P D u := by rw [cz_sc]; exact Lam_sc P D _ _
/- English proof (translation)
Rewrite using `[cc_sc]`. Conclude with `Lams_sc P D _ _`.
-/
theorem Lams_cc (u : ℂ) : Lams P D u * cc P D = cc P D * Lams P D u := by rw [cc_sc]; exact Lams_sc P D _ _
/- English proof (translation)
Rewrite using `[cz_sc]`. Conclude with `Lams_sc P D _ _`.
-/
theorem Lams_cz (u : ℂ) : Lams P D u * cz P D = cz P D * Lams P D u := by rw [cz_sc]; exact Lams_sc P D _ _

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem half (u v : ℂ) : (u + 1 / 2) - (v + 1 / 2) = u - v := by ring

/- English proof (translation)
Establish `h` using `commutator_identity_one (nabA P D) (cc P D) (ggA P D) (ggiA P D) (xA P D u) (abelian₂ P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2) (N_g P D) (x_N P D u) (gG P D) (Gg P D) (cc_g P D) (kap_sc P D _ _) (kap_sc P D _ _) (kap_cc P D _) (Lam_sc P D _ _) (Lam_sc P D _ _) (by rw [half …`. Rewrite `h` using `[half]`. Rewrite using `[t22, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]`. Conclude with `h`.
-/
theorem lowering_relation_diagonal_left (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P D u * lA P D v - lA P D v * t22 P D u) = -(t22 P D u * (lA P D u - lA P D v)) := by
  have h := commutator_identity_one (nabA P D) (cc P D) (ggA P D) (ggiA P D) (xA P D u) (abelian₂ P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2)
    (N_g P D) (x_N P D u) (gG P D) (Gg P D) (cc_g P D) (kap_sc P D _ _) (kap_sc P D _ _) (kap_cc P D _)
    (Lam_sc P D _ _) (Lam_sc P D _ _) (by rw [half]; exact L3.Lam1 P D u v hu hv)
  rw [half] at h
  rw [t22, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h

/- English proof (translation)
Establish `h` using `commutator_identity_two (nabA P D) (cc P D) (ggiA P D) (kap P D fun π => (xC P π (u + 1))⁻¹) (abelian₂ P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2) (qC P u) (N_G P D) (kap_nab P D _).symm (G_cc P D) (kap_sc P D _ _) (kap_cc P D _) (Lam_sc P D _ _) (Lam_sc P D _ _) (by rw [half …`. Rewrite `h` using `[half]`. Rewrite using `[dA, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]`. Conclude with `h`.
-/
theorem lowering_relation_diagonal_right (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (dA P D u * lA P D v - lA P D v * dA P D u) = dA P D u * (lA P D u - lA P D v) := by
  have h := commutator_identity_two (nabA P D) (cc P D) (ggiA P D) (kap P D fun π => (xC P π (u + 1))⁻¹) (abelian₂ P D u) (abelian₂ P D v)
    (u + 1 / 2) (v + 1 / 2) (qC P u)
    (N_G P D) (kap_nab P D _).symm (G_cc P D) (kap_sc P D _ _) (kap_cc P D _)
    (Lam_sc P D _ _) (Lam_sc P D _ _) (by rw [half]; exact L3.Lam2 P D u v hu hv)
  rw [half] at h
  rw [dA, lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h

/- English proof (translation)
Establish `h` using `raising_pair_relation (nabA P D) (cc P D) (ggiA P D) (abelian₂ P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2) (N_cc P D) (N_G P D) (N_Lam P D hS u) (N_Lam P D hS v) (G_cc P D) (Lam_cc P D u) (Lam_cc P D v) (Lam_sc P D _ _) (Lam_sc P D _ _) (by rw [half]; exact L3.Lam3 P D hC hP …`. Rewrite `h` using `[half]`. Rewrite using `[lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]`. Conclude with `h`.
-/
theorem commutator_l_sq (hC : SSComm) (hS : NabSS) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (lA P D u * lA P D v - lA P D v * lA P D u) = (lA P D u - lA P D v) * (lA P D u - lA P D v) := by
  have h := raising_pair_relation (nabA P D) (cc P D) (ggiA P D) (abelian₂ P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2)
    (N_cc P D) (N_G P D) (N_Lam P D hS u) (N_Lam P D hS v) (G_cc P D) (Lam_cc P D u) (Lam_cc P D v)
    (Lam_sc P D _ _) (Lam_sc P D _ _) (by rw [half]; exact L3.Lam3 P D hC hP u v hu hv)
  rw [half] at h
  rw [lA_eq, lA_eq, lowering_constant_eq_shift, lowering_constant_eq_shift]
  exact h

def hh (u : ℂ) : Ty P → ℂ := fun π => qC P u / (xC P π u * xC P π (u + 1))

/- English proof (translation)
Establish `hcurv : nabsA P D * nabA P D = nabA P D * nabsA P D + (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) * (ggiA P D * ggiA P D)`. Rewrite using `[← mul_assoc, ← hK P D]`. Normalize the expressions using the abelian group laws. Establish `h` using `commutator_identity_four (nabA P D) (nabsA P D) (cc P D) (cz P D) (ggiA P D) (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) (Lams P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2) (P.TT : ℂ) hcurv (Ns_cc P D) (N_cz P D) (N_G P D) (Ns_G P D) (Ns_Lam P D hS v) (N_Lams P D hS u) (G_ …`. Rewrite using `[mt_eq, lA_eq, lowering_constant_eq_shift, h, L4.Lam4 P D hP u v hN hM]`.

Establish `e1 : ∀ f : Ty P → ℂ, ggiA P D * (ggiA P D * kap P D f) = kap P D f * (ggiA P D * ggiA P D)` using `fun f => by`. Rewrite using `[← mul_assoc, G_sc, sc_mul, kap_sc]`. Establish `e2 : ∀ z : ℂ, z • (ggiA P D * ggiA P D) = kap P D (fun _ => z) * (ggiA P D * ggiA P D)` using `fun z => by`. Establish `: kap P D (fun _ => z) = algebraMap ℂ (A P D) z` using `(kap P D).commutes z`. Rewrite using `[this, Algebra.smul_def]`.

Rewrite using `[e1, e2, ← add_mul, ← add_mul, ← map_add, ← map_add, ← smul_mul_assoc, ← map_smul]`. Use `congr 2`. Use function extensionality and compare the values at `π`. Establish `hs` using `WB.scalar_partial_fraction_identity P hP π u v hu hv`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hh]`.

Rewrite using `[← hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relD4core (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P D u * lA P D v - lA P D v * mt P D u) = kap P D (hh P v - hh P u) * (ggiA P D * ggiA P D) := by
  have hcurv : nabsA P D * nabA P D = nabA P D * nabsA P D +
      (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) * (ggiA P D * ggiA P D) := by
    rw [← mul_assoc, ← hK P D]; abel
  have h := commutator_identity_four (nabA P D) (nabsA P D) (cc P D) (cz P D) (ggiA P D) (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ))
    (Lams P D u) (abelian₂ P D v) (u + 1 / 2) (v + 1 / 2) (P.TT : ℂ) hcurv (Ns_cc P D) (N_cz P D) (N_G P D) (Ns_G P D)
    (Ns_Lam P D hS v) (N_Lams P D hS u) (G_cc P D) (G_cz P D) (cz_cc P D) (Lam_cc P D v) (Lam_cz P D v) (Lam_sc P D _ _)
    (Lams_cc P D u) (Lams_cz P D u) (Lams_sc P D _ _)
  rw [mt_eq, lA_eq, lowering_constant_eq_shift, h, L4.Lam4 P D hP u v hN hM]
  have e1 : ∀ f : Ty P → ℂ, ggiA P D * (ggiA P D * kap P D f) = kap P D f * (ggiA P D * ggiA P D) := fun f => by
    rw [← mul_assoc, G_sc, sc_mul, kap_sc]
  have e2 : ∀ z : ℂ, z • (ggiA P D * ggiA P D) = kap P D (fun _ => z) * (ggiA P D * ggiA P D) := fun z => by
    have : kap P D (fun _ => z) = algebraMap ℂ (A P D) z := (kap P D).commutes z
    rw [this, Algebra.smul_def]
  rw [e1, e2, ← add_mul, ← add_mul, ← map_add, ← map_add, ← smul_mul_assoc, ← map_smul]
  congr 2
  funext π
  have hs := WB.scalar_partial_fraction_identity P hP π u v hu hv
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hh]
  rw [← hs]
  push_cast
  ring

/- English proof (translation)
Establish `h` using `relD4core P D hN hM hS hK hP u v hu hv`. Establish `e : (u - v) • (t22 P D v * mt P D u * lA P D v * t22 P D u - t22 P D v * lA P D v * mt P D u * t22 P D u) = t22 P D v * ((u - v) • (mt P D u * lA P D v - lA P D v * mt P D u)) * t22 P D u`. Simplify using `only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]`. Rewrite using `[e, h, t22, t22, xA, xA, absSand _ _ _ _ _ (gG P D) (Gg P D) (kap_sc P D _ _) (kap_sc P D _ _) (kap_sc P D _ _) (kap_sc P D _ _)]`. Establish `e3 : dA P D v * (ggA P D * kap P D fun π => xC P π u) = kap P D fun π => qC P v * (xC P π (v + 1))⁻¹ * xC P π u`.

Rewrite using `[dA, smul_mul_assoc, mul_assoc, lc (kap_g P D _), lc1 (Gg P D), kap_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e4 : (ggA P D * kap P D fun π => xC P π v) * dA P D u = kap P D fun π => xC P π v * (qC P u * (xC P π (u + 1))⁻¹)`. Rewrite using `[dA, mul_smul_comm, mul_assoc, lc (kap_G P D _), lc1 (gG P D), kap_mul, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3, e4, kap_mul, kap_mul, ← map_sub]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Establish `h1` using `xC_ne P hu π`.

Establish `h2` using `xC_ne P hv π`. Establish `h3` using `coordinate_shift_ne_zero P hu π`. Establish `h4` using `coordinate_shift_ne_zero P hv π`. Simplify using `only [Pi.mul_apply, Pi.sub_apply, hh]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mixed_relation_diagonal_four (hN : SSNorm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P D v * mt P D u * lA P D v * t22 P D u - t22 P D v * lA P D v * mt P D u * t22 P D u) =
      dA P D v * t22 P D u - t22 P D v * dA P D u := by
  have h := relD4core P D hN hM hS hK hP u v hu hv
  have e : (u - v) • (t22 P D v * mt P D u * lA P D v * t22 P D u - t22 P D v * lA P D v * mt P D u * t22 P D u) =
      t22 P D v * ((u - v) • (mt P D u * lA P D v - lA P D v * mt P D u)) * t22 P D u := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [e, h, t22, t22, xA, xA, absSand _ _ _ _ _ (gG P D) (Gg P D) (kap_sc P D _ _) (kap_sc P D _ _) (kap_sc P D _ _) (kap_sc P D _ _)]
  have e3 : dA P D v * (ggA P D * kap P D fun π => xC P π u) = kap P D fun π => qC P v * (xC P π (v + 1))⁻¹ * xC P π u := by
    rw [dA, smul_mul_assoc, mul_assoc, lc (kap_g P D _), lc1 (Gg P D), kap_mul, ← map_smul]
    congr 1
    funext π
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  have e4 : (ggA P D * kap P D fun π => xC P π v) * dA P D u = kap P D fun π => xC P π v * (qC P u * (xC P π (u + 1))⁻¹) := by
    rw [dA, mul_smul_comm, mul_assoc, lc (kap_G P D _), lc1 (gG P D), kap_mul, ← map_smul]
    congr 1
    funext π
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul]; ring
  rw [e3, e4, kap_mul, kap_mul, ← map_sub]
  congr 1
  funext π
  have h1 := xC_ne P hu π
  have h2 := xC_ne P hv π
  have h3 := coordinate_shift_ne_zero P hu π
  have h4 := coordinate_shift_ne_zero P hv π
  simp only [Pi.mul_apply, Pi.sub_apply, hh]
  field_simp

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

namespace Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

open Matrix Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

section Abs3
variable {B : Type*} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Combine the equalities or inequalities in the calculation `calc a * K1 * (b * K2) = a * b * (K1 * K2) := by rw [mul_assoc, lc h1, mul_assoc] _ = b * a * (K2 * K1) := by rw [hab, hK] _ = b * K2 * (a * K1) := by rw [mul_assoc b K2, lc h2, mul_assoc]`.
-/
theorem absCC (a b K1 K2 : B) (hab : a * b = b * a) (hK : K1 * K2 = K2 * K1) (h1 : K1 * b = b * K1)
    (h2 : K2 * a = a * K2) : (a * K1) * (b * K2) = (b * K2) * (a * K1) :=
  calc a * K1 * (b * K2) = a * b * (K1 * K2) := by rw [mul_assoc, lc h1, mul_assoc]
    _ = b * a * (K2 * K1) := by rw [hab, hK]
    _ = b * K2 * (a * K1) := by rw [mul_assoc b K2, lc h2, mul_assoc]

end Abs3

noncomputable section

variable (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)]

/- English proof (translation)
Unfold `xC`. Rewrite using `[← starRingEnd_apply, map_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => by simp`.
-/
theorem star_xC (π : Ty P) (u : ℂ) : star (xC P π (star u)) = xC P π u := by
  unfold xC
  rw [← starRingEnd_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => by simp

/- English proof (translation)
Unfold `qC`. Rewrite using `[← starRingEnd_apply, map_mul, map_prod]`. Use `congr 1`. Simplify using the standard rewrite rules. Conclude with `Finset.prod_congr rfl fun i _ => by simp [map_ofNat]`.
-/
theorem star_qC (u : ℂ) : star (qC P (star u)) = qC P u := by
  unfold qC
  rw [← starRingEnd_apply, map_mul, map_prod]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun i _ => by simp [map_ofNat]

/- English proof (translation)
Rewrite using `[t22, t22, star_mul, star_g, xA, xA, star_kap, kap_g]`. Use `congr 2`. Use function extensionality and compare the values at `π`. Conclude with `star_xC P π u`.
-/
theorem star_t22 (u : ℂ) : star (t22 P D (star u)) = t22 P D u := by
  rw [t22, t22, star_mul, star_g, xA, xA, star_kap, kap_g]
  congr 2
  funext π
  exact star_xC P π u

/- English proof (translation)
Rewrite using `[dA, dA, star_smul, star_qC, star_mul, star_G, star_kap, kap_G]`. Use `congr 3`. Use function extensionality and compare the values at `π`. Establish `: star u + 1 = star (u + 1)` using `by simp`. Rewrite using `[star_inv₀, this, star_xC]`.
-/
theorem star_dA (u : ℂ) : star (dA P D (star u)) = dA P D u := by
  rw [dA, dA, star_smul, star_qC, star_mul, star_G, star_kap, kap_G]
  congr 3
  funext π
  have : star u + 1 = star (u + 1) := by simp
  rw [star_inv₀, this, star_xC]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem star_lA (u : ℂ) : star (lA P D (star u)) = mt P D u := rfl

/- English proof (translation)
Establish `h` using `congrArg star (lowering_relation_diagonal_left P D (star u) (star v) (good_star P hu) (good_star P hv))`. Simplify using `only [star_smul, star_sub, star_mul, star_neg, star_star, star_t22, star_lA] at h`. Simplify using `only [mul_sub, sub_mul, smul_sub] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`.
-/
theorem commutator_t22_m (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (t22 P D u * mt P D v - mt P D v * t22 P D u) = (mt P D u - mt P D v) * t22 P D u := by
  have h := congrArg star (lowering_relation_diagonal_left P D (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_t22, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h

/- English proof (translation)
Establish `h` using `congrArg star (lowering_relation_diagonal_right P D (star u) (star v) (good_star P hu) (good_star P hv))`. Simplify using `only [star_smul, star_sub, star_mul, star_neg, star_star, star_dA, star_lA] at h`. Simplify using `only [mul_sub, sub_mul, smul_sub] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`.
-/
theorem commutator_d_m (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (dA P D u * mt P D v - mt P D v * dA P D u) = -((mt P D u - mt P D v) * dA P D u) := by
  have h := congrArg star (lowering_relation_diagonal_right P D (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_dA, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h

/- English proof (translation)
Establish `h` using `congrArg star (commutator_l_sq P D hC hS hP (star u) (star v) (good_star P hu) (good_star P hv))`. Simplify using `only [star_smul, star_sub, star_mul, star_neg, star_star, star_lA] at h`. Simplify using `only [mul_sub, sub_mul, smul_sub] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`.
-/
theorem raising_relation_self (hC : SSComm) (hS : NabSS) (hP : P.OK) (u v : ℂ) (hu : Good P u) (hv : Good P v) :
    (u - v) • (mt P D u * mt P D v - mt P D v * mt P D u) = -((mt P D u - mt P D v) * (mt P D u - mt P D v)) := by
  have h := congrArg star (commutator_l_sq P D hC hS hP (star u) (star v) (good_star P hu) (good_star P hv))
  simp only [star_smul, star_sub, star_mul, star_neg, star_star, star_lA] at h
  simp only [mul_sub, sub_mul, smul_sub] at h ⊢
  linear_combination (norm := module) (-1 : ℂ) • h

/- English proof (translation)
Rewrite using `[t21, t22, lA_eq, diagonal_lowering_absorb (ggA P D) (ggiA P D) (xA P D u) _ _ (gG P D) (kap_G P D _), L4.xLam P D hu]`.
-/
theorem nf21 {u : ℂ} (hu : Good P u) : t21 P D u = t22 P D u * lA P D u := by
  rw [t21, t22, lA_eq, diagonal_lowering_absorb (ggA P D) (ggiA P D) (xA P D u) _ _ (gG P D) (kap_G P D _), L4.xLam P D hu]

/- English proof (translation)
Rewrite using `[t12, t22, mt_eq, raising_operator_absorb _ _ _ _ _ _ _ (Ns_g P D) (x_Ns P D u) (Gg P D) (cz_g P D) (kap_cz P D _).symm (Lams_sc P D _ _), L4.Lamsx P D hu, raising_constant_eq_shift]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nf12 {u : ℂ} (hu : Good P u) : t12 P D u = mt P D u * t22 P D u := by
  rw [t12, t22, mt_eq, raising_operator_absorb _ _ _ _ _ _ _ (Ns_g P D) (x_Ns P D u) (Gg P D) (cz_g P D) (kap_cz P D _).symm (Lams_sc P D _ _),
    L4.Lamsx P D hu, raising_constant_eq_shift]
  congr 4
  ring

/- English proof (translation)
Rewrite using `[raising_constant_eq_shift]`. Simplify using `only [mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, x_Ns]`. Rewrite using `[xA, kap_cz]`.
-/
theorem coordinate_commute_raising_constant (u v : ℂ) : xA P D u * m0A P D v = m0A P D v * xA P D u := by
  rw [raising_constant_eq_shift]
  simp only [mul_sub, sub_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, x_Ns]
  rw [xA, kap_cz]

/- English proof (translation)
Unfold `S12`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, G_sc, Ss_sc, ← mul_assoc, kap_sc, mul_assoc]`.
-/
theorem S12_commute_GGinv (u : ℂ) : S12 P D u * ggiA P D = ggiA P D * S12 P D u := by
  unfold S12
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, G_sc, Ss_sc, ← mul_assoc, kap_sc, mul_assoc]

/- English proof (translation)
Rewrite using `[← nf12 P D hu, t12, lA_eq, absN _ _ _ _ _ _ _ (coordinate_commute_raising_constant P D u u) (kap_G P D _) (S12_commute_GGinv P D u), L4.xLam P D hu, L4.upper_sum_mul_lambda P D hP hu hN, t11, mul_add]`. Establish `e : ggiA P D * (kap P D fun π => wC P π u) = dA P D u + ggiA P D * kap P D fun π => ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1)`. Rewrite using `[dA, ← mul_smul_comm, ← map_smul, ← mul_add, ← map_add]`. Use `congr 2`. Use function extensionality and compare the values at `π`.

Rewrite using `[WB.wC_eq P hP π u hu]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.
-/
theorem nf11 (hN : SSNorm) (hP : P.OK) {u : ℂ} (hu : Good P u) :
    t11 P D u = dA P D u + mt P D u * t22 P D u * lA P D u := by
  rw [← nf12 P D hu, t12, lA_eq, absN _ _ _ _ _ _ _ (coordinate_commute_raising_constant P D u u) (kap_G P D _) (S12_commute_GGinv P D u), L4.xLam P D hu,
    L4.upper_sum_mul_lambda P D hP hu hN, t11, mul_add]
  have e : ggiA P D * (kap P D fun π => wC P π u) = dA P D u + ggiA P D * kap P D fun π =>
      ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℝ) : ℂ) * xEx P {l} π u / (u + (rho P π l : ℂ) + 1) := by
    rw [dA, ← mul_smul_comm, ← map_smul, ← mul_add, ← map_add]
    congr 2
    funext π
    rw [WB.wC_eq P hP π u hu]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  rw [e]
  abel

/- English proof (translation)
The claim follows from `absCC _ _ _ _ rfl (kap_comm P D _ _) (kap_g P D _) (kap_g P D _)`.
-/
theorem comm_tt (u v : ℂ) : t22 P D v * t22 P D u = t22 P D u * t22 P D v :=
  absCC _ _ _ _ rfl (kap_comm P D _ _) (kap_g P D _) (kap_g P D _)

/- English proof (translation)
Simplify using `only [dA, smul_mul_assoc, mul_smul_comm]`. Rewrite using `[smul_comm, absCC _ _ _ _ rfl (kap_comm P D _ _) (kap_G P D _) (kap_G P D _)]`.
-/
theorem comm_dd (u v : ℂ) : dA P D v * dA P D u = dA P D u * dA P D v := by
  simp only [dA, smul_mul_assoc, mul_smul_comm]
  rw [smul_comm, absCC _ _ _ _ rfl (kap_comm P D _ _) (kap_G P D _) (kap_G P D _)]

/- English proof (translation)
Simplify using `only [dA, t22, xA, smul_mul_assoc, mul_smul_comm]`. Rewrite using `[absCC _ _ _ _ ((Gg P D).trans (gG P D).symm) (kap_comm P D _ _) (kap_g P D _) (kap_G P D _)]`.
-/
theorem comm_dt (u v : ℂ) : dA P D v * t22 P D u = t22 P D u * dA P D v := by
  simp only [dA, t22, xA, smul_mul_assoc, mul_smul_comm]
  rw [absCC _ _ _ _ ((Gg P D).trans (gG P D).symm) (kap_comm P D _ _) (kap_g P D _) (kap_G P D _)]

/- English proof (translation)
Establish `eU : ∀ {y : ℂ}, Good P y → QQr P D y = !![dA P D y + mt P D y * t22 P D y * lA P D y, mt P D y * t22 P D y; t22 P D y * lA P D y, t22 P D y]` using `fun {y} hy => by`. Rewrite using `[QQr, nf11 P D hN hP hy, nf12 P D hy, nf21 P D hy]`. Establish `e : v - u = -(u - v)` using `by ring`. Rewrite using `[eU hu, eU hv]`. Use `GA.gauss_rtt (u - v) h0 h1 h2 (t22 P D u) (t22 P D v) (dA P D u) (dA P D v) (lA P D u) (lA P D v) (mt P D u) (mt P D v) (comm_tt P D u v) (comm_dd P D u v) (comm_dt P D u v) (comm_dt P D v u) (lowering_relation_diagonal_left P D u v hu hv) ?_ (lowering_relation_diagonal_right P D …` and prove the remaining obligations.

Establish `h` using `lowering_relation_diagonal_left P D v u hv hu`. Rewrite `h` using `[e]`. Simplify using `only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`. Establish `h` using `lowering_relation_diagonal_right P D v u hv hu`.

Rewrite `h` using `[e]`. Simplify using `only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`. Establish `h` using `commutator_t22_m P D v u hv hu`. Rewrite `h` using `[e]`.

Simplify using `only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`. Establish `h` using `commutator_d_m P D v u hv hu`. Rewrite `h` using `[e]`. Simplify using `only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢`.

Take the linear combination `(norm := module) (-1 : ℂ) • h`. Establish `h` using `mixed_relation_diagonal_four P D hN hM hS hK hP v u hv hu`. Rewrite `h` using `[e]`. Simplify using `only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢`. Take the linear combination `(norm := module) (-1 : ℂ) • h`.
-/
theorem generic (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) (hP : P.OK)
    (u v : ℂ) (hu : Good P u) (hv : Good P v) (h0 : u - v ≠ 0) (h1 : u - v ≠ 1) (h2 : u - v ≠ -1)
    (i j k l : Fin 2) :
    (u - v) • (QQr P D u i j * QQr P D v k l - QQr P D v k l * QQr P D u i j) =
      QQr P D u k j * QQr P D v i l - QQr P D v k j * QQr P D u i l := by
  have eU : ∀ {y : ℂ}, Good P y → QQr P D y =
      !![dA P D y + mt P D y * t22 P D y * lA P D y, mt P D y * t22 P D y; t22 P D y * lA P D y, t22 P D y] := fun {y} hy => by
    rw [QQr, nf11 P D hN hP hy, nf12 P D hy, nf21 P D hy]
  have e : v - u = -(u - v) := by ring
  rw [eU hu, eU hv]
  refine GA.gauss_rtt (u - v) h0 h1 h2 (t22 P D u) (t22 P D v) (dA P D u) (dA P D v) (lA P D u) (lA P D v) (mt P D u) (mt P D v)
    (comm_tt P D u v) (comm_dd P D u v) (comm_dt P D u v) (comm_dt P D v u)
    (lowering_relation_diagonal_left P D u v hu hv) ?_ (lowering_relation_diagonal_right P D u v hu hv) ?_ (commutator_t22_m P D u v hu hv) ?_ (commutator_d_m P D u v hu hv) ?_
    (commutator_l_sq P D hC hS hP u v hu hv) (raising_relation_self P D hC hS hP u v hu hv) (mixed_relation_diagonal_four P D hN hM hS hK hP u v hu hv) ?_ i j k l
  · have h := lowering_relation_diagonal_left P D v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := lowering_relation_diagonal_right P D v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := commutator_t22_m P D v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := commutator_d_m P D v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h
  · have h := mixed_relation_diagonal_four P D hN hM hS hK hP v u hv hu
    rw [e] at h
    simp only [mul_sub, sub_mul, smul_sub, neg_smul] at h ⊢
    linear_combination (norm := module) (-1 : ℂ) • h

/- English proof (translation)
Introduce `P D _ hP` and use `PC.entries_of_generic P D fun u v hu hv h0 h1 h2 i j k l => generic P D hN hC hM hS hK hP u v hu hv h0 h1 h2 i j k l`.
-/
theorem entries_of (hN : SSNorm) (hC : SSComm) (hM : SSMixed) (hS : NabSS) (hK : Curvature) : QQRTTEntries :=
  fun P D _ hP => PC.entries_of_generic P D fun u v hu hv h0 h1 h2 i j k l =>
    generic P D hN hC hM hS hK hP u v hu hv h0 h1 h2 i j k l

end

end Formalism.FourierDecayAlt.P.MAx1.ModelAlgebraRelations

namespace Formalism.FourierDecayAlt.P.MAx1

/- English proof (translation)
The claim follows from `ModelAlgebraRelations.entries_of sSNorm sSComm sSMixed nabSS curvature`.
-/
theorem qQRTTEntries : QQRTTEntries := ModelAlgebraRelations.entries_of sSNorm sSComm sSMixed nabSS curvature

/- English proof (translation)
The claim follows from `ModelAlgebraRelations.PC.ofEntries`.
-/
theorem qQRTTOfEntries : QQRTTOfEntries := ModelAlgebraRelations.PC.ofEntries

/- English proof (translation)
The claim follows from `qQRTTOfEntries qQRTTEntries`.
-/
theorem qQRTT : QQRTT := qQRTTOfEntries qQRTTEntries

end Formalism.FourierDecayAlt.P.MAx1

end

section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx1.D7

section PartT

open  Formalism.FourierDecayAlt Finset
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_eq (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) :
    kap P D f = Matrix.diagonal fun π => algebraMap ℂ (D.Pr) (f π) := rfl

/- English proof (translation)
Use `show kap P D f * Matrix.diagonal d = Matrix.diagonal d * kap P D f`. Rewrite using `[kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `Algebra.commutes _ _`.
-/
theorem kap_comm_diagonal (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) (d : Ty P → D.Pr) :
    Commute (kap P D f) (Matrix.diagonal d) := by
  show kap P D f * Matrix.diagonal d = Matrix.diagonal d * kap P D f
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

/- English proof (translation)
Establish `: sc P D w = Matrix.diagonal fun _ => w` using `by simp [sc, Matrix.scalar_apply]`. Rewrite using `[this]`. Conclude with `kap_comm_diagonal P D f _`.
-/
theorem kap_comm_sc (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) (w : D.Pr) : Commute (kap P D f) (sc P D w) := by
  have : sc P D w = Matrix.diagonal fun _ => w := by simp [sc, Matrix.scalar_apply]
  rw [this]; exact kap_comm_diagonal P D f _

/- English proof (translation)
The claim follows from `kap_comm_diagonal P D f _`.
-/
theorem kap_comm_nab (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) : Commute (kap P D f) (nabA P D) := kap_comm_diagonal P D f _

/- English proof (translation)
The claim follows from `kap_comm_diagonal P D f _`.
-/
theorem kap_comm_nabs (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) : Commute (kap P D f) (nabsA P D) := kap_comm_diagonal P D f _

/- English proof (translation)
Use `show kap P D f * kap P D g = kap P D g * kap P D f`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem kap_comm_kap (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f g : Ty P → ℂ) : Commute (kap P D f) (kap P D g) := by
  show kap P D f * kap P D g = kap P D g * kap P D f
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Unfold `xC xEx`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem xC_eq (P : Par) (π : Ty P) (Y : ℂ) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    xC P π Y = xEx P {l} π Y * (Y + (rho P π l : ℂ)) := by
  unfold xC xEx
  calc ∏ i ∈ Icc 1 (P.k - 1), (Y + (rho P π i : ℂ))
      = (∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + (rho P π i : ℂ))) * ∏ i ∈ {l}, (Y + (rho P π i : ℂ)) :=
        (Finset.prod_sdiff (Finset.singleton_subset_iff.2 hl)).symm
    _ = _ := by rw [Finset.prod_singleton]

/- English proof (translation)
Unfold `xEx`. Establish `hset : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}) \ {j}`. Use extensionality with `i`. Simplify using `only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]`. The claim follows by propositional logic.

Establish `hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) \ {l}` using `Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hj, by simpa using hjl⟩)`. Rewrite using `[hset]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem xEx_pair (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {l} π Y = xEx P {l, j} π Y * (Y + (rho P π j : ℂ)) := by
  unfold xEx
  have hset : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}) \ {j} := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) \ {l} :=
    Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hj, by simpa using hjl⟩)
  rw [hset]
  calc ∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + (rho P π i : ℂ))
      = (∏ i ∈ (Icc 1 (P.k - 1) \ {l}) \ {j}, (Y + (rho P π i : ℂ))) * ∏ i ∈ {j}, (Y + (rho P π i : ℂ)) :=
        (Finset.prod_sdiff hsub).symm
    _ = _ := by rw [Finset.prod_singleton]

/- English proof (translation)
Rewrite using `[Finset.pair_comm l j]`. Conclude with `xEx_pair P π Y j l hl (Ne.symm hjl)`.
-/
theorem xEx_pair' (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {j} π Y = xEx P {l, j} π Y * (Y + (rho P π l : ℂ)) := by
  rw [Finset.pair_comm l j]; exact xEx_pair P π Y j l hl (Ne.symm hjl)

/- English proof (translation)
Unfold `xEx`. Use `Finset.prod_congr rfl ?_` and prove the remaining obligations. Introduce `i hi`. Establish `hi'` using `Finset.mem_sdiff.1 hi`. Establish `hne : i ≠ l` using `fun h => hi'.2 (h ▸ hl)`.

Rewrite using `[hR P l π π' hU i hi'.1, if_neg hne, add_zero]`.
-/
theorem xEx_up (hR : RhoUp) (P : Par) (l : ℕ) (π π' : Ty P) (hU : Up P l π π') (ex : Finset ℕ) (hl : l ∈ ex)
    (Y : ℂ) : xEx P ex π' Y = xEx P ex π Y := by
  unfold xEx
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hi' := Finset.mem_sdiff.1 hi
  have hne : i ≠ l := fun h => hi'.2 (h ▸ hl)
  rw [hR P l π π' hU i hi'.1, if_neg hne, add_zero]

/- English proof (translation)
Rewrite using `[hR P l π π' hU l hl, if_pos rfl]`.
-/
theorem rho_up (hR : RhoUp) (P : Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π π' : Ty P) (hU : Up P l π π') :
    rho P π' l = rho P π l + 1 := by
  rw [hR P l π π' hU l hl, if_pos rfl]

/- English proof (translation)
The claim follows from `hSh P D l _ _ (fun π π' hU => xEx_up hR P l π π' hU ex hl Y)`.
-/
theorem sh_same (hSh : SSShift) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (ex : Finset ℕ) (hl : l ∈ ex) (Y : ℂ) :
    (kap P D fun π => xEx P ex π Y) * SS P D l = SS P D l * kap P D fun π => xEx P ex π Y :=
  hSh P D l _ _ (fun π π' hU => xEx_up hR P l π π' hU ex hl Y)

/- English proof (translation)
The claim follows from `hSh P D l _ _ (fun π π' hU => by show xC P π' Y = _ rw [xC_eq P π' Y l hl, xEx_up hR P l π π' hU {l} (Finset.mem_singleton_self l), rho_up hR P l hl π π' hU] push_cast; ring)`.
-/
theorem shift_x_identity (hSh : SSShift) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (Y : ℂ) :
    xA P D Y * SS P D l = SS P D l * kap P D fun π => xEx P {l} π Y * (Y + 1 + (rho P π l : ℂ)) :=
  hSh P D l _ _ (fun π π' hU => by
    show xC P π' Y = _
    rw [xC_eq P π' Y l hl, xEx_up hR P l π π' hU {l} (Finset.mem_singleton_self l), rho_up hR P l hl π π' hU]
    push_cast; ring)

/- English proof (translation)
The claim follows from `hSh P D j _ _ (fun π π' hU => by show xEx P {l} π' Y = _ rw [xEx_pair P π' Y l j hj hjl, xEx_up hR P j π π' hU {l, j} (by simp), rho_up hR P j hj π π' hU] push_cast; ring)`.
-/
theorem sh_pair (hSh : SSShift) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) (Y : ℂ) :
    (kap P D fun π => xEx P {l} π Y) * SS P D j = SS P D j * kap P D fun π => xEx P {l, j} π Y * (Y + 1 + (rho P π j : ℂ)) :=
  hSh P D j _ _ (fun π π' hU => by
    show xEx P {l} π' Y = _
    rw [xEx_pair P π' Y l j hj hjl, xEx_up hR P j π π' hU {l, j} (by simp), rho_up hR P j hj π π' hU]
    push_cast; ring)

/- English proof (translation)
Rewrite using `[l0A, Algebra.smul_def]`.
-/
theorem lowering_constant_eq_shift (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : l0A P D Y = -nabA P D - (Y + 1 / 2) • (zbA P D * ggiA P D) := by
  rw [l0A, Algebra.smul_def]

section abs

variable {R : Type*} [Ring R] [Algebra ℂ R]

/- English proof (translation)
Establish `h1 : G * (-N - cu • b) - zb = -(G * N) - (cu + 1) • zb`. Rewrite using `[mul_sub, mul_neg, mul_smul_comm, hGb]`. Use `module`. Establish `h2 : G * N * b = zb * N - zb * b`. Rewrite using `[mul_assoc, hNb, mul_sub, ← mul_assoc, ← mul_assoc, hGb]`.

Rewrite using `[h1]`. Simplify using `only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, h2]`. Use `module`.
-/
theorem absW (G b zb N : R) (hGb : G * b = zb) (hNb : N * b = b * N - b * b) (cu cv : ℂ) :
    (G * (-N - cu • b) - zb) * (-N - cv • b) =
      G * N * N + (cu + cv + 1) • (zb * N) + (cu * cv) • (zb * b) := by
  have h1 : G * (-N - cu • b) - zb = -(G * N) - (cu + 1) • zb := by
    rw [mul_sub, mul_neg, mul_smul_comm, hGb]; module
  have h2 : G * N * b = zb * N - zb * b := by
    rw [mul_assoc, hNb, mul_sub, ← mul_assoc, ← mul_assoc, hGb]
  rw [h1]
  simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, h2]
  module

/- English proof (translation)
Rewrite using `[sub_mul, neg_mul, smul_mul_assoc, hNG, hbG, mul_sub, mul_neg, mul_smul_comm]`. Normalize the expressions using the abelian group laws.
-/
theorem absLG (G b zb N : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b) (c : ℂ) :
    (-N - c • b) * G = G * (-N - c • b) - zb := by
  rw [sub_mul, neg_mul, smul_mul_assoc, hNG, hbG, mul_sub, mul_neg, mul_smul_comm]; abel

/- English proof (translation)
Establish `hc : (G * (-N - cu • b) - zb) * X' = X' * (G * (-N - cu • b) - zb)` using `((hG.mul_right ((hN.neg_right).sub_right (hb.smul_right cu))).sub_right hzb).eq.symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[absLG G b zb N hNG hbG]`. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [hc]; simp only [mul_assoc]`.
-/
theorem absA (G b zb N X X' : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b)
    (hG : Commute X' G) (hb : Commute X' b) (hN : Commute X' N) (hzb : Commute X' zb) (cu cv : ℂ) :
    (G * X * (-N - cu • b)) * (G * X' * (-N - cv • b)) =
      G * (X * X') * ((G * (-N - cu • b) - zb) * (-N - cv • b)) := by
  have hc : (G * (-N - cu • b) - zb) * X' = X' * (G * (-N - cu • b) - zb) :=
    ((hG.mul_right ((hN.neg_right).sub_right (hb.smul_right cu))).sub_right hzb).eq.symm
  calc (G * X * (-N - cu • b)) * (G * X' * (-N - cv • b))
      = G * X * ((-N - cu • b) * G) * X' * (-N - cv • b) := by simp only [mul_assoc]
    _ = G * X * ((G * (-N - cu • b) - zb) * X') * (-N - cv • b) := by
        rw [absLG G b zb N hNG hbG]; simp only [mul_assoc]
    _ = _ := by rw [hc]; simp only [mul_assoc]

/- English proof (translation)
Rewrite using `[← mul_assoc, hNzb, mul_assoc, hNGi, mul_sub, ← mul_assoc zb Gi N, mul_assoc zb Gi (zb * Gi), ← mul_assoc Gi zb Gi, hc]`.
-/
theorem absNb (zb Gi N : R) (hNzb : N * zb = zb * N) (hNGi : N * Gi = Gi * N - zb * Gi * Gi)
    (hc : Gi * zb = zb * Gi) : N * (zb * Gi) = (zb * Gi) * N - (zb * Gi) * (zb * Gi) := by
  rw [← mul_assoc, hNzb, mul_assoc, hNGi, mul_sub, ← mul_assoc zb Gi N, mul_assoc zb Gi (zb * Gi),
    ← mul_assoc Gi zb Gi, hc]

/- English proof (translation)
Rewrite using `[sub_mul, neg_mul, smul_mul_assoc, hNS, hbS, mul_add, mul_sub, mul_neg, mul_smul_comm]`. Normalize the expressions using the abelian group laws.
-/
theorem absLS (b N S : R) (hNS : N * S = S * N - b * S) (hbS : b * S = S * b) (c : ℂ) :
    (-N - c • b) * S = S * ((-N - c • b) + b) := by
  rw [sub_mul, neg_mul, smul_mul_assoc, hNS, hbS, mul_add, mul_sub, mul_neg, mul_smul_comm]; abel

/- English proof (translation)
Establish `hE : ((-N - c • b) + b) * E = E * ((-N - c • b) + b)` using `(((hEN.neg_right).sub_right (hEb.smul_right c)).add_right hEb).eq.symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem weighted_sum_difference_identity (G b N S X Xp E : R) (hNS : N * S = S * N - b * S) (hbS : b * S = S * b)
    (hXS : X * S = S * Xp) (hSG : S * G = G * S) (hEN : Commute E N) (hEb : Commute E b) (c : ℂ) :
    G * X * (-N - c • b) * (S * E) = S * G * (Xp * E * ((-N - c • b) + b)) := by
  have hE : ((-N - c • b) + b) * E = E * ((-N - c • b) + b) :=
    (((hEN.neg_right).sub_right (hEb.smul_right c)).add_right hEb).eq.symm
  calc G * X * (-N - c • b) * (S * E) = G * X * ((-N - c • b) * S) * E := by simp only [mul_assoc]
    _ = G * (X * S) * (((-N - c • b) + b) * E) := by rw [absLS b N S hNS hbS]; simp only [mul_assoc]
    _ = G * (S * Xp) * (E * ((-N - c • b) + b)) := by rw [hXS, hE]
    _ = (G * S) * (Xp * E * ((-N - c • b) + b)) := by simp only [mul_assoc]
    _ = _ := by rw [← hSG]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem mul_assoc_commute_middle (G S X E L : R) (hEG : E * G = G * E) :
    (S * E) * (G * X * L) = S * G * (E * X * L) := by
  calc (S * E) * (G * X * L) = S * (E * G) * (X * L) := by simp only [mul_assoc]
    _ = S * (G * E) * (X * L) := by rw [hEG]
    _ = _ := by simp only [mul_assoc]

/- English proof (translation)
Establish `e1` using `congrArg (fun f => κ f * N) h1`. Establish `e2` using `congrArg (fun f => κ f * b) h2`. Simplify using `only [map_add, map_sub, map_smul, add_mul, sub_mul, smul_mul_assoc] at e1 e2`. Simplify using `only [mul_add, mul_sub, mul_neg, mul_smul_comm]`. Take the linear combination `(norm := module) -e1 + e2`.
-/
theorem absCombo {C : Type*} [CommRing C] [Algebra ℂ C] (κ : C →ₐ[ℂ] R) (N b : R) (φ1 φ2 ψ1 ψ2 : C) (cu cv : ℂ)
    (h1 : φ1 + φ2 = ψ1 + ψ2) (h2 : (1 - cu) • φ1 - cv • φ2 = (1 - cv) • ψ1 - cu • ψ2) :
    κ φ1 * ((-N - cu • b) + b) + κ φ2 * (-N - cv • b) = κ ψ1 * ((-N - cv • b) + b) + κ ψ2 * (-N - cu • b) := by
  have e1 := congrArg (fun f => κ f * N) h1
  have e2 := congrArg (fun f => κ f * b) h2
  simp only [map_add, map_sub, map_smul, add_mul, sub_mul, smul_mul_assoc] at e1 e2
  simp only [mul_add, mul_sub, mul_neg, mul_smul_comm]
  linear_combination (norm := module) -e1 + e2

/- English proof (translation)
Establish `hc : ∑ l ∈ s, ∑ j ∈ s, D l j = ∑ l ∈ s, ∑ j ∈ s, D j l` using `Finset.sum_comm`. Establish `h2 : ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : (2 : ℂ) • ∑ l ∈ s, ∑ j ∈ s, D l j = 0` using `by rw [two_smul]; exact h2`. Conclude with `(smul_eq_zero.1 h3).resolve_left two_ne_zero`.
-/
theorem sum_anti {M : Type*} [AddCommGroup M] [Module ℂ M] (s : Finset ℕ) (D : ℕ → ℕ → M)
    (h : ∀ l ∈ s, ∀ j ∈ s, D l j + D j l = 0) : ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by
  have hc : ∑ l ∈ s, ∑ j ∈ s, D l j = ∑ l ∈ s, ∑ j ∈ s, D j l := Finset.sum_comm
  have h2 : ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by
    calc ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D l j
        = ∑ l ∈ s, ∑ j ∈ s, D l j + ∑ l ∈ s, ∑ j ∈ s, D j l := by rw [← hc]
      _ = ∑ l ∈ s, ∑ j ∈ s, (D l j + D j l) := by simp only [Finset.sum_add_distrib]
      _ = 0 := Finset.sum_eq_zero (fun l hl => Finset.sum_eq_zero (fun j hj => h l hl j hj))
  have h3 : (2 : ℂ) • ∑ l ∈ s, ∑ j ∈ s, D l j = 0 := by rw [two_smul]; exact h2
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

end abs

/- English proof (translation)
Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [h]; simp only [mul_assoc]`.
-/
theorem TT_eq (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l j : ℕ) (f g f' : Ty P → ℂ) (h : kap P D f * SS P D j = SS P D j * kap P D f') :
    (SS P D l * kap P D f) * (SS P D j * kap P D g) = SS P D l * SS P D j * kap P D (f' * g) := by
  rw [map_mul]
  calc (SS P D l * kap P D f) * (SS P D j * kap P D g) = SS P D l * (kap P D f * SS P D j) * kap P D g := by
        simp only [mul_assoc]
    _ = _ := by rw [h]; simp only [mul_assoc]

/- English proof (translation)
Take `⟨_, _, hNzb, _, hNG, hNGi, _⟩` from `hLN P D`. Take `⟨hcomm, _, _, _, _, _, hGGi, hGiG, _⟩` from `hLF P D`. Establish `mzb : zbA P D ∈ fnsA P D` using `by unfold fnsA; simp`. Establish `mG : ggA P D ∈ fnsA P D` using `by unfold fnsA; simp`. Establish `mGi : ggiA P D ∈ fnsA P D` using `by unfold fnsA; simp`.

Establish `hGb : ggA P D * (zbA P D * ggiA P D) = zbA P D`. Rewrite using `[← mul_assoc, hcomm _ mG _ mzb, mul_assoc, hGGi, mul_one]`. Establish `hbG : (zbA P D * ggiA P D) * ggA P D = ggA P D * (zbA P D * ggiA P D)`. Rewrite using `[hGb, mul_assoc, hGiG, mul_one]`. Establish `hNb : nabA P D * (zbA P D * ggiA P D) = (zbA P D * ggiA P D) * nabA P D - (zbA P D * ggiA P D) * (zbA P D * ggiA P D)` using `absNb _ _ _ hNzb hNGi (hcomm _ mGi _ mzb)`.

Establish `cX : ∀ w : ℂ, Commute (xA P D w) (ggA P D) ∧ Commute (xA P D w) (zbA P D * ggiA P D) ∧ Commute (xA P D w) (nabA P D) ∧ Commute (xA P D w) (zbA P D)` using `fun w => ⟨kap_comm_sc P D _ _, (kap_comm_sc P D _ _).mul_right (kap_comm_sc P D _ _), kap_comm_nab P D _, kap_comm_sc P D _ _⟩`. Establish `hXX : xA P D u * xA P D v = xA P D v * xA P D u` using `(kap_comm_kap P D _ _).eq`. Rewrite using `[lowering_constant_eq_shift, lowering_constant_eq_shift, absA _ _ _ _ _ _ hNG hbG (cX v).1 (cX v).2.1 (cX v).2.2.1 (cX v).2.2.2, absA _ _ _ _ _ _ hNG hbG (cX u).1 (cX u).2.1 (cX u).2.2.1 (cX u).2.2.2, absW _ _ _ _ hGb hNb, absW _ _ _ _ hGb hNb, hXX, add_comm (u + 1 / 2) (v + 1 / …`.
-/
theorem compA (hLN : LevNab) (hLF : LevFns) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (u v : ℂ) :
    (ggA P D * xA P D u * l0A P D u) * (ggA P D * xA P D v * l0A P D v) =
      (ggA P D * xA P D v * l0A P D v) * (ggA P D * xA P D u * l0A P D u) := by
  obtain ⟨_, _, hNzb, _, hNG, hNGi, _⟩ := hLN P D
  obtain ⟨hcomm, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P D
  have mzb : zbA P D ∈ fnsA P D := by unfold fnsA; simp
  have mG : ggA P D ∈ fnsA P D := by unfold fnsA; simp
  have mGi : ggiA P D ∈ fnsA P D := by unfold fnsA; simp
  have hGb : ggA P D * (zbA P D * ggiA P D) = zbA P D := by
    rw [← mul_assoc, hcomm _ mG _ mzb, mul_assoc, hGGi, mul_one]
  have hbG : (zbA P D * ggiA P D) * ggA P D = ggA P D * (zbA P D * ggiA P D) := by
    rw [hGb, mul_assoc, hGiG, mul_one]
  have hNb : nabA P D * (zbA P D * ggiA P D) = (zbA P D * ggiA P D) * nabA P D - (zbA P D * ggiA P D) * (zbA P D * ggiA P D) :=
    absNb _ _ _ hNzb hNGi (hcomm _ mGi _ mzb)
  have cX : ∀ w : ℂ, Commute (xA P D w) (ggA P D) ∧ Commute (xA P D w) (zbA P D * ggiA P D) ∧ Commute (xA P D w) (nabA P D) ∧
      Commute (xA P D w) (zbA P D) := fun w =>
    ⟨kap_comm_sc P D _ _, (kap_comm_sc P D _ _).mul_right (kap_comm_sc P D _ _), kap_comm_nab P D _, kap_comm_sc P D _ _⟩
  have hXX : xA P D u * xA P D v = xA P D v * xA P D u := (kap_comm_kap P D _ _).eq
  rw [lowering_constant_eq_shift, lowering_constant_eq_shift,
    absA _ _ _ _ _ _ hNG hbG (cX v).1 (cX v).2.1 (cX v).2.2.1 (cX v).2.2.2,
    absA _ _ _ _ _ _ hNG hbG (cX u).1 (cX u).2.1 (cX u).2.2.1 (cX u).2.2.2,
    absW _ _ _ _ hGb hNb, absW _ _ _ _ hGb hNb, hXX,
    add_comm (u + 1 / 2) (v + 1 / 2), mul_comm (u + 1 / 2) (v + 1 / 2)]

/- English proof (translation)
Establish `hNS` using `(hN P D l hl).1`. Establish `hbS : (zbA P D * ggiA P D) * SS P D l = SS P D l * (zbA P D * ggiA P D)` using `((hSc P D l D.zbP).mul_right (hSc P D l (D.ggiP P.TT))).eq.symm`. Establish `hSG : SS P D l * ggA P D = ggA P D * SS P D l` using `(hSc P D l (D.ggP P.TT)).eq`. Establish `cE : ∀ w : ℂ, Commute (kap P D fun π => xEx P {l} π w) (nabA P D) ∧ Commute (kap P D fun π => xEx P {l} π w) (zbA P D * ggiA P D) ∧ (kap P D fun π => xEx P {l} π w) * ggA P D = ggA P D * kap P D fun π => xEx P {l} π w` using `fun w => ⟨kap_comm_nab P D _, (kap_comm_sc P D _ _).mul_right (kap_comm_sc P D _ _), (kap_comm_sc P D _ _).eq⟩`. Rewrite using `[lowering_constant_eq_shift, lowering_constant_eq_shift, weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P D l hl u) hSG (cE v).1 (cE v).2.1, weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P D l hl v) hSG (cE u).1 ( …`.

Use `congrArg (fun t => SS P D l * ggA P D * t) ?_` and prove the remaining obligations. Unfold `xA`. Rewrite using `[← map_mul, ← map_mul, ← map_mul, ← map_mul]`. Apply `absCombo` to reduce the goal to its premises. Use function extensionality and compare the values at `π`.

Simplify using `only [Pi.add_apply, Pi.mul_apply]`. Rewrite using `[xC_eq P π u l hl, xC_eq P π v l hl]`. Expand and normalize the polynomial expressions, which then agree. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]`.

Rewrite using `[xC_eq P π u l hl, xC_eq P π v l hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem compB (hSc : SSScalar) (hSh : SSShift) (hN : NabSS) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (u v : ℂ) (l : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) :
    (ggA P D * xA P D u * l0A P D u) * (SS P D l * kap P D fun π => xEx P {l} π v) +
      (SS P D l * kap P D fun π => xEx P {l} π u) * (ggA P D * xA P D v * l0A P D v) =
    (ggA P D * xA P D v * l0A P D v) * (SS P D l * kap P D fun π => xEx P {l} π u) +
      (SS P D l * kap P D fun π => xEx P {l} π v) * (ggA P D * xA P D u * l0A P D u) := by
  have hNS := (hN P D l hl).1
  have hbS : (zbA P D * ggiA P D) * SS P D l = SS P D l * (zbA P D * ggiA P D) :=
    ((hSc P D l D.zbP).mul_right (hSc P D l (D.ggiP P.TT))).eq.symm
  have hSG : SS P D l * ggA P D = ggA P D * SS P D l := (hSc P D l (D.ggP P.TT)).eq
  have cE : ∀ w : ℂ, Commute (kap P D fun π => xEx P {l} π w) (nabA P D) ∧
      Commute (kap P D fun π => xEx P {l} π w) (zbA P D * ggiA P D) ∧
      (kap P D fun π => xEx P {l} π w) * ggA P D = ggA P D * kap P D fun π => xEx P {l} π w := fun w =>
    ⟨kap_comm_nab P D _, (kap_comm_sc P D _ _).mul_right (kap_comm_sc P D _ _), (kap_comm_sc P D _ _).eq⟩
  rw [lowering_constant_eq_shift, lowering_constant_eq_shift,
    weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P D l hl u) hSG (cE v).1 (cE v).2.1,
    weighted_sum_difference_identity _ _ _ _ _ _ _ hNS hbS (shift_x_identity hSh hR P D l hl v) hSG (cE u).1 (cE u).2.1,
    mul_assoc_commute_middle _ _ _ _ _ (cE u).2.2, mul_assoc_commute_middle _ _ _ _ _ (cE v).2.2, ← mul_add, ← mul_add]
  refine congrArg (fun t => SS P D l * ggA P D * t) ?_
  unfold xA
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  apply absCombo
  · funext π
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [xC_eq P π u l hl, xC_eq P π v l hl]; ring
  · funext π
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [xC_eq P π u l hl, xC_eq P π v l hl]; ring

/- English proof (translation)
Rewrite using `[TT_eq P D l l _ _ _ (sh_same hSh hR P D l {l} (Finset.mem_singleton_self l) u), TT_eq P D l l _ _ _ (sh_same hSh hR P D l {l} (Finset.mem_singleton_self l) v), mul_comm]`.
-/
theorem compC_diag (hSh : SSShift) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (u v : ℂ) (l : ℕ) :
    (SS P D l * kap P D fun π => xEx P {l} π u) * (SS P D l * kap P D fun π => xEx P {l} π v) =
      (SS P D l * kap P D fun π => xEx P {l} π v) * (SS P D l * kap P D fun π => xEx P {l} π u) := by
  rw [TT_eq P D l l _ _ _ (sh_same hSh hR P D l {l} (Finset.mem_singleton_self l) u),
    TT_eq P D l l _ _ _ (sh_same hSh hR P D l {l} (Finset.mem_singleton_self l) v), mul_comm]

/- English proof (translation)
Rewrite using `[TT_eq P D l j _ _ _ (sh_pair hSh hR P D l j hj hjl u), TT_eq P D l j _ _ _ (sh_pair hSh hR P D l j hj hjl v), TT_eq P D j l _ _ _ (sh_pair hSh hR P D j l hl (Ne.symm hjl) u), TT_eq P D j l _ _ _ (sh_pair hSh hR P D j l hl (Ne.symm hjl) v), ← mul_sub, ← mul_sub, ← map_sub, ← map_ …`. Establish `h12 : ((fun π => xEx P {l, j} π u * (u + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π v) - ((fun π => xEx P {l, j} π v * (v + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π u) = -((fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) * fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} …`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]`. Rewrite using `[xEx_pair' P π v l j hl hjl, xEx_pair' P π u l j hl hjl]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h34 : ((fun π => xEx P {j, l} π u * (u + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π v) - ((fun π => xEx P {j, l} π v * (v + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π u) = (fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) * fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π …`. Use function extensionality and compare the values at `π`. Simplify using `only [Pi.sub_apply, Pi.mul_apply]`.

Rewrite using `[xEx_pair P π v l j hj hjl, xEx_pair P π u l j hj hjl, Finset.pair_comm j l]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h12, h34, map_neg, map_mul, map_mul, ← mul_assoc (SS P D j * SS P D l), hC P D hP l hl j hj hjl, mul_neg, mul_assoc (SS P D l * SS P D j), neg_add_cancel]`.
-/
theorem compC_off (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (u v : ℂ) (l j : ℕ)
    (hl : l ∈ Icc 1 (P.k - 1)) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    ((SS P D l * kap P D fun π => xEx P {l} π u) * (SS P D j * kap P D fun π => xEx P {j} π v) -
      (SS P D l * kap P D fun π => xEx P {l} π v) * (SS P D j * kap P D fun π => xEx P {j} π u)) +
    ((SS P D j * kap P D fun π => xEx P {j} π u) * (SS P D l * kap P D fun π => xEx P {l} π v) -
      (SS P D j * kap P D fun π => xEx P {j} π v) * (SS P D l * kap P D fun π => xEx P {l} π u)) = 0 := by
  rw [TT_eq P D l j _ _ _ (sh_pair hSh hR P D l j hj hjl u), TT_eq P D l j _ _ _ (sh_pair hSh hR P D l j hj hjl v),
    TT_eq P D j l _ _ _ (sh_pair hSh hR P D j l hl (Ne.symm hjl) u),
    TT_eq P D j l _ _ _ (sh_pair hSh hR P D j l hl (Ne.symm hjl) v), ← mul_sub, ← mul_sub, ← map_sub, ← map_sub]
  have h12 : ((fun π => xEx P {l, j} π u * (u + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π v) -
      ((fun π => xEx P {l, j} π v * (v + 1 + (rho P π j : ℂ))) * fun π => xEx P {j} π u) =
      -((fun π => ((rho P π j - rho P π l + 1 : ℝ) : ℂ)) *
        fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π v)) := by
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
    rw [xEx_pair' P π v l j hl hjl, xEx_pair' P π u l j hl hjl]
    push_cast; ring
  have h34 : ((fun π => xEx P {j, l} π u * (u + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π v) -
      ((fun π => xEx P {j, l} π v * (v + 1 + (rho P π l : ℂ))) * fun π => xEx P {l} π u) =
      (fun π => ((rho P π j - rho P π l - 1 : ℝ) : ℂ)) *
        fun π => (u - v) * (xEx P {l, j} π u * xEx P {l, j} π v) := by
    funext π
    simp only [Pi.sub_apply, Pi.mul_apply]
    rw [xEx_pair P π v l j hj hjl, xEx_pair P π u l j hj hjl, Finset.pair_comm j l]
    push_cast; ring
  rw [h12, h34, map_neg, map_mul, map_mul, ← mul_assoc (SS P D j * SS P D l), hC P D hP l hl j hj hjl, mul_neg,
    mul_assoc (SS P D l * SS P D j), neg_add_cancel]

/- English proof (translation)
Unfold `weightedSumBis`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]`. Simplify using `only [← Finset.sum_sub_distrib]`. Apply `sum_anti` to reduce the goal to its premises. Introduce `l hl j hj`.

Distinguish the cases in `hjl : j = l`. Substitute `hjl` using the available equality. Rewrite using `[compC_diag hSh hR P D u v j, sub_self, add_zero]`. Conclude with `compC_off hSh hC hR P D hP u v l j hl hj hjl`.
-/
theorem compC (hSh : SSShift) (hC : SSComm) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (u v : ℂ) :
    weightedSumBis P D u * weightedSumBis P D v = weightedSumBis P D v * weightedSumBis P D u := by
  unfold weightedSumBis
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib]
  apply sum_anti
  intro l hl j hj
  by_cases hjl : j = l
  · subst hjl
    rw [compC_diag hSh hR P D u v j, sub_self, add_zero]
  · exact compC_off hSh hC hR P D hP u v l j hl hj hjl

/- English proof (translation)
Introduce `P D _ hP u v`. Use `show t21 P D u * t21 P D v = t21 P D v * t21 P D u`. Establish `hA` using `compA hLN hLF P D u v`. Establish `hB : (ggA P D * xA P D u * l0A P D u) * weightedSumBis P D v + weightedSumBis P D u * (ggA P D * xA P D v * l0A P D v) = (ggA P D * xA P D v * l0A P D v) * weightedSumBis P D u + weightedSumBis P D v * (ggA P D * xA P D u * l0A P D u)`. Unfold `weightedSumBis`.

Rewrite using `[Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl (fun l hl => compB hSc hSh hN hR P D u v l hl)`. Establish `hCC` using `compC hSh hC hR P D hP u v`. Unfold `t21`. Rewrite using `[add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hA, hCC]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem lower_left_commute_of_laws (hSc : SSScalar) (hSh : SSShift) (hC : SSComm) (hN : NabSS) (hLN : LevNab) (hLF : LevFns)
    (hR : RhoUp) : T21Commute := by
  intro P D _ hP u v
  show t21 P D u * t21 P D v = t21 P D v * t21 P D u
  have hA := compA hLN hLF P D u v
  have hB : (ggA P D * xA P D u * l0A P D u) * weightedSumBis P D v + weightedSumBis P D u * (ggA P D * xA P D v * l0A P D v) =
      (ggA P D * xA P D v * l0A P D v) * weightedSumBis P D u + weightedSumBis P D v * (ggA P D * xA P D u * l0A P D u) := by
    unfold weightedSumBis
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l hl => compB hSc hSh hN hR P D u v l hl)
  have hCC := compC hSh hC hR P D hP u v
  unfold t21
  rw [add_mul, mul_add, mul_add, add_mul, mul_add, mul_add, hA, hCC]
  calc _ = (ggA P D * xA P D v * l0A P D v) * (ggA P D * xA P D u * l0A P D u) +
        ((ggA P D * xA P D u * l0A P D u) * weightedSumBis P D v + weightedSumBis P D u * (ggA P D * xA P D v * l0A P D v)) +
        weightedSumBis P D v * weightedSumBis P D u := by abel
    _ = _ := by rw [hB]; abel

end PartT

section PartF

open  Formalism.FourierDecayAlt Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

noncomputable section

/- English proof (translation)
Rewrite using `[natDegree_le_iff_coeff_eq_zero]`. Introduce `m hm`. Rewrite using `[coeff_sub]`. Break down `Nat.lt_or_ge (N + 2) m with h | h` into its components or cases. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]`.

Establish `: m = N + 1 ∨ m = N + 2` using `by omega`. Break down `this with rfl | rfl` into its components or cases. Rewrite `hn` using `[nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), d1, d2]`. Establish `e : N + 2 - 1 = N + 1` using `by omega`. Rewrite `hn` using `[e]`.

Rewrite using `[hn, sub_self]`. Establish `a1 : p1.coeff (N + 2) = 1` using `by rw [← d1]; exact h1.coeff_natDegree`. Establish `a2 : p2.coeff (N + 2) = 1` using `by rw [← d2]; exact h2.coeff_natDegree`. Rewrite using `[a1, a2, sub_self]`.
-/
theorem natDegree_sub_le_of_next (p1 p2 : ℂ[X]) (N : ℕ) (h1 : p1.Monic) (h2 : p2.Monic)
    (d1 : p1.natDegree = N + 2) (d2 : p2.natDegree = N + 2) (hn : p1.nextCoeff = p2.nextCoeff) :
    (p1 - p2).natDegree ≤ N := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [coeff_sub]
  rcases Nat.lt_or_ge (N + 2) m with h | h
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega), sub_zero]
  · have : m = N + 1 ∨ m = N + 2 := by omega
    rcases this with rfl | rfl
    · rw [nextCoeff_of_natDegree_pos (by omega), nextCoeff_of_natDegree_pos (by omega), d1, d2] at hn
      have e : N + 2 - 1 = N + 1 := by omega
      rw [e] at hn
      rw [hn, sub_self]
    · have a1 : p1.coeff (N + 2) = 1 := by rw [← d1]; exact h1.coeff_natDegree
      have a2 : p2.coeff (N + 2) = 1 := by rw [← d2]; exact h2.coeff_natDegree
      rw [a1, a2, sub_self]

def pa (s : Finset ℕ) (ρ : ℕ → ℂ) : ℂ[X] := ∏ i ∈ s, (X + C (ρ i))

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)`.
-/
theorem pa_monic (s : Finset ℕ) (ρ : ℕ → ℂ) : (pa s ρ).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

/- English proof (translation)
Unfold `pa`. Rewrite using `[natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]`. Simplify using the standard rewrite rules.
-/
theorem pa_natDegree (s : Finset ℕ) (ρ : ℕ → ℂ) : (pa s ρ).natDegree = s.card := by
  unfold pa
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp

/- English proof (translation)
Unfold `pa`. Rewrite using `[Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]`. Simplify using the standard rewrite rules.
-/
theorem pa_nextCoeff (s : Finset ℕ) (ρ : ℕ → ℂ) : (pa s ρ).nextCoeff = ∑ i ∈ s, ρ i := by
  unfold pa
  rw [Monic.nextCoeff_prod _ _ (fun i _ => monic_X_add_C _)]
  simp

/- English proof (translation)
Simplify using `[pa, eval_prod]`.
-/
theorem pa_eval (s : Finset ℕ) (ρ : ℕ → ℂ) (Y : ℂ) : (pa s ρ).eval Y = ∏ i ∈ s, (Y + ρ i) := by
  simp [pa, eval_prod]

/- English proof (translation)
The claim follows from `(Finset.mul_prod_erase s _ hl).symm`.
-/
theorem pa_erase (s : Finset ℕ) (ρ : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    pa s ρ = (X + C (ρ l)) * pa (s.erase l) ρ := (Finset.mul_prod_erase s _ hl).symm

/- English proof (translation)
The claim follows from `Finset.dvd_prod_of_mem _ hl`.
-/
theorem fac_dvd (s : Finset ℕ) (ρ : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) : X + C (ρ l) ∣ pa s ρ :=
  Finset.dvd_prod_of_mem _ hl

/- English proof (translation)
Unfold `pa`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises. Introduce `i hi j hj hij show IsCoprime (X + C (ρ i)) (X + C (ρ j))`. Establish `e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a)` using `by intro a; simp`. Rewrite using `[e, e]`.

Apply `isCoprime_X_sub_C_of_isUnit_sub` to reduce the goal to its premises. Apply `IsUnit.mk0` to reduce the goal to its premises. Introduce `h0`. Conclude with `hij (hinj i hi j hj (by linear_combination -h0))`. Introduce `l hl`.

Establish `e : (X + C (ρ l) : ℂ[X]) = X - C (-ρ l)` using `by simp`. Rewrite using `[e, dvd_iff_isRoot]`. Conclude with `h l hl`.
-/
theorem pa_dvd (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j) (F : ℂ[X])
    (h : ∀ l ∈ s, F.eval (-ρ l) = 0) : pa s ρ ∣ F := by
  unfold pa
  apply Finset.prod_dvd_of_coprime
  · intro i hi j hj hij
    show IsCoprime (X + C (ρ i)) (X + C (ρ j))
    have e : ∀ a : ℂ, (X + C a : ℂ[X]) = X - C (-a) := by intro a; simp
    rw [e, e]
    apply isCoprime_X_sub_C_of_isUnit_sub
    apply IsUnit.mk0
    intro h0
    exact hij (hinj i hi j hj (by linear_combination -h0))
  · intro l hl
    have e : (X + C (ρ l) : ℂ[X]) = X - C (-ρ l) := by simp
    rw [e, dvd_iff_isRoot]
    exact h l hl

def DD (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) : ℂ[X] :=
  C c * q1 + (∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) -
    (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1)))

/- English proof (translation)
Simplify using `only [DD, eval_sub, eval_add, eval_mul, eval_C, eval_finsetSum, pa_eval]`.
-/
theorem DD_eval (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (Y : ℂ) :
    (DD s ρ c q1 N M).eval Y =
    c * q1.eval Y + (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) -
      (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) := by
  simp only [DD, eval_sub, eval_add, eval_mul, eval_C, eval_finsetSum, pa_eval]

/- English proof (translation)
Rewrite using `[DD_eval]`. Establish `z : ∏ j ∈ s, (-ρ l + ρ j) = 0` using `Finset.prod_eq_zero hl (by ring)`. Establish `z2 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-ρ l + ρ j)) * ∏ j ∈ s.erase m, (-ρ l + (ρ j + 1)))) = 0` using `Finset.sum_eq_zero (fun j _ => by rw [z]; ring)`. Establish `z3 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1)))) = M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1)))`. Apply `Finset.sum_eq_single l` to reduce the goal to its premises.

Introduce `j _ hj`. Rewrite using `[Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring`. Introduce `h`. Conclude with `absurd hl h`. Rewrite using `[z2, z3, sub_zero]`.
-/
theorem DD_eval_a (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-ρ l) =
    c * q1.eval (-ρ l) + M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by
  rw [DD_eval]
  have z : ∏ j ∈ s, (-ρ l + ρ j) = 0 := Finset.prod_eq_zero hl (by ring)
  have z2 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-ρ l + ρ j)) * ∏ j ∈ s.erase m, (-ρ l + (ρ j + 1)))) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [z]; ring)
  have z3 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1)))) =
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) := by
    apply Finset.sum_eq_single l
    · intro j _ hj
      rw [Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring
    · intro h; exact absurd hl h
  rw [z2, z3, sub_zero]

/- English proof (translation)
Rewrite using `[DD_eval]`. Establish `z : ∏ j ∈ s, (-(ρ l + 1) + (ρ j + 1)) = 0` using `Finset.prod_eq_zero hl (by ring)`. Establish `z2 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s, (-(ρ l + 1) + (ρ j + 1)))) = 0` using `Finset.sum_eq_zero (fun j _ => by rw [z]; ring)`. Establish `z3 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase m, (-(ρ l + 1) + (ρ j + 1)))) = N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1)))`. Apply `Finset.sum_eq_single l` to reduce the goal to its premises.

Introduce `j _ hj`. Rewrite using `[Finset.prod_eq_zero (s := s.erase j) (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring`. Introduce `h`. Conclude with `absurd hl h`. Rewrite using `[z2, z3, add_zero]`.
-/
theorem DD_eval_b (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) (l : ℕ) (hl : l ∈ s) :
    (DD s ρ c q1 N M).eval (-(ρ l + 1)) =
    c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) := by
  rw [DD_eval]
  have z : ∏ j ∈ s, (-(ρ l + 1) + (ρ j + 1)) = 0 := Finset.prod_eq_zero hl (by ring)
  have z2 : (∑ m ∈ s, M m * ((∏ j ∈ s.erase m, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s, (-(ρ l + 1) + (ρ j + 1)))) = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [z]; ring)
  have z3 : (∑ m ∈ s, N m * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase m, (-(ρ l + 1) + (ρ j + 1)))) =
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) := by
    apply Finset.sum_eq_single l
    · intro j _ hj
      rw [Finset.prod_eq_zero (s := s.erase j) (i := l) (Finset.mem_erase.2 ⟨fun h => hj h.symm, hl⟩) (by ring)]; ring
    · intro h; exact absurd hl h
  rw [z2, z3, add_zero]

/- English proof (translation)
Take `⟨D1, hD1⟩` from `pa_dvd s ρ hinj (DD s ρ c q1 N M) (fun l hl => by rw [DD_eval_a _ _ _ _ _ _ l hl]; exact H1 l hl)`. Establish `key : pa s (fun i => ρ i + 1) ∣ D1`. Apply `pa_dvd s (fun i => ρ i + 1) (fun i hi j hj h => hinj i hi j hj (add_right_cancel h))` to reduce the goal to its premises. Introduce `l hl`. Use `show D1.eval (-(ρ l + 1)) = 0`.

Establish `hD0 : (DD s ρ c q1 N M).eval (-(ρ l + 1)) = 0`. Rewrite using `[DD_eval_b _ _ _ _ _ _ l hl]`. Conclude with `H2 l hl`. Distinguish the cases in `hdeg : ∃ m ∈ s, ρ m = ρ l + 1`. Take `⟨m, hm, hml⟩` from `hdeg`.

Take `⟨hN, hM, hq⟩` from `H3 l hl m hm hml`. Establish `ht0 : (X + C (ρ l + 1) : ℂ[X]) ≠ 0` using `(monic_X_add_C _).ne_zero`. Establish `hta : ∀ s' : Finset ℕ, m ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' ρ`. Introduce `s' h`. Use `fac_dvd s' ρ m h` as an intermediate fact.

Rewrite `this` using `[hml]`. Then use the resulting hypothesis. Establish `htb : ∀ s' : Finset ℕ, l ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' (fun i => ρ i + 1)` using `fun s' h => fac_dvd s' (fun i => ρ i + 1) l h`. Establish `htt : (X + C (ρ l + 1) : ℂ[X]) * (X + C (ρ l + 1)) ∣ DD s ρ c q1 N M`. Unfold `DD`. Use `dvd_sub (dvd_add (Dvd.dvd.mul_left hq _) (Finset.dvd_sum ?_)) (Finset.dvd_sum ?_)` and prove the remaining obligations.

Introduce `j hj`. Distinguish the cases in `hjm : j = m`. Rewrite using `[hjm, hM]`. Simplify using the standard rewrite rules. Conclude with `Dvd.dvd.mul_left (mul_dvd_mul (hta _ (Finset.mem_erase.2 ⟨fun h => hjm h.symm, hm⟩)) (htb _ hl)) _`.

Introduce `j hj`. Distinguish the cases in `hjl : j = l`. Rewrite using `[hjl, hN]`. Simplify using the standard rewrite rules. Conclude with `Dvd.dvd.mul_left (mul_dvd_mul (hta _ hm) (htb _ (Finset.mem_erase.2 ⟨fun h => hjl h.symm, hl⟩))) _`.

Establish `hpa : pa s ρ = (X + C (ρ l + 1)) * pa (s.erase m) ρ` using `by rw [pa_erase s ρ m hm, hml]`. Rewrite `htt` using `[hD1, hpa, mul_assoc]`. Establish `h3 : (X + C (ρ l + 1) : ℂ[X]) ∣ pa (s.erase m) ρ * D1` using `(mul_dvd_mul_iff_left ht0).1 htt`. Establish `e : (X + C (ρ l + 1) : ℂ[X]) = X - C (-(ρ l + 1))` using `by rw [C_neg, sub_neg_eq_add]`. Rewrite `h3` using `[e, dvd_iff_isRoot, IsRoot.def, eval_mul, pa_eval]`.

Break down `mul_eq_zero.1 h3 with h4 | h4` into its components or cases. It suffices to derive a contradiction. Rewrite `h4` using `[Finset.prod_eq_zero_iff]`. Take `⟨j, hj, hj0⟩` from `h4`. Establish `: ρ j = ρ m` using `by rw [hml]; linear_combination hj0`.

Conclude with `(Finset.mem_erase.1 hj).1 (hinj j (Finset.mem_erase.1 hj).2 m hm this)`. Conclude with `h4`. Establish `hdeg : ∀ j ∈ s, ρ j ≠ ρ l + 1` using `fun j hj h => hdeg ⟨j, hj, h⟩`. Rewrite `hD0` using `[hD1, eval_mul, pa_eval]`. Break down `mul_eq_zero.1 hD0 with h4 | h4` into its components or cases.

It suffices to derive a contradiction. Rewrite `h4` using `[Finset.prod_eq_zero_iff]`. Take `⟨j, hj, hj0⟩` from `h4`. Conclude with `hdeg j hj (by linear_combination hj0)`. Conclude with `h4`.

Rewrite using `[hD1]`. Conclude with `mul_dvd_mul_left _ key`.
-/
theorem DD_dvd (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1) :
    pa s ρ * pa s (fun i => ρ i + 1) ∣ DD s ρ c q1 N M := by
  obtain ⟨D1, hD1⟩ := pa_dvd s ρ hinj (DD s ρ c q1 N M)
    (fun l hl => by rw [DD_eval_a _ _ _ _ _ _ l hl]; exact H1 l hl)
  have key : pa s (fun i => ρ i + 1) ∣ D1 := by
    apply pa_dvd s (fun i => ρ i + 1) (fun i hi j hj h => hinj i hi j hj (add_right_cancel h))
    intro l hl
    show D1.eval (-(ρ l + 1)) = 0
    have hD0 : (DD s ρ c q1 N M).eval (-(ρ l + 1)) = 0 := by
      rw [DD_eval_b _ _ _ _ _ _ l hl]; exact H2 l hl
    by_cases hdeg : ∃ m ∈ s, ρ m = ρ l + 1
    · obtain ⟨m, hm, hml⟩ := hdeg
      obtain ⟨hN, hM, hq⟩ := H3 l hl m hm hml
      have ht0 : (X + C (ρ l + 1) : ℂ[X]) ≠ 0 := (monic_X_add_C _).ne_zero
      have hta : ∀ s' : Finset ℕ, m ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' ρ := by
        intro s' h; have := fac_dvd s' ρ m h; rwa [hml] at this
      have htb : ∀ s' : Finset ℕ, l ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' (fun i => ρ i + 1) :=
        fun s' h => fac_dvd s' (fun i => ρ i + 1) l h
      have htt : (X + C (ρ l + 1) : ℂ[X]) * (X + C (ρ l + 1)) ∣ DD s ρ c q1 N M := by
        unfold DD
        refine dvd_sub (dvd_add (Dvd.dvd.mul_left hq _) (Finset.dvd_sum ?_)) (Finset.dvd_sum ?_)
        · intro j hj
          by_cases hjm : j = m
          · rw [hjm, hM]; simp
          · exact Dvd.dvd.mul_left (mul_dvd_mul (hta _ (Finset.mem_erase.2 ⟨fun h => hjm h.symm, hm⟩)) (htb _ hl)) _
        · intro j hj
          by_cases hjl : j = l
          · rw [hjl, hN]; simp
          · exact Dvd.dvd.mul_left (mul_dvd_mul (hta _ hm) (htb _ (Finset.mem_erase.2 ⟨fun h => hjl h.symm, hl⟩))) _
      have hpa : pa s ρ = (X + C (ρ l + 1)) * pa (s.erase m) ρ := by rw [pa_erase s ρ m hm, hml]
      rw [hD1, hpa, mul_assoc] at htt
      have h3 : (X + C (ρ l + 1) : ℂ[X]) ∣ pa (s.erase m) ρ * D1 := (mul_dvd_mul_iff_left ht0).1 htt
      have e : (X + C (ρ l + 1) : ℂ[X]) = X - C (-(ρ l + 1)) := by rw [C_neg, sub_neg_eq_add]
      rw [e, dvd_iff_isRoot, IsRoot.def, eval_mul, pa_eval] at h3
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h4
        obtain ⟨j, hj, hj0⟩ := h4
        have : ρ j = ρ m := by rw [hml]; linear_combination hj0
        exact (Finset.mem_erase.1 hj).1 (hinj j (Finset.mem_erase.1 hj).2 m hm this)
      · exact h4
    · have hdeg : ∀ j ∈ s, ρ j ≠ ρ l + 1 := fun j hj h => hdeg ⟨j, hj, h⟩
      rw [hD1, eval_mul, pa_eval] at hD0
      rcases mul_eq_zero.1 hD0 with h4 | h4
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h4
        obtain ⟨j, hj, hj0⟩ := h4
        exact hdeg j hj (by linear_combination hj0)
      · exact h4
  rw [hD1]
  exact mul_dvd_mul_left _ key

/- English proof (translation)
Establish `hdv` using `DD_dvd s ρ hinj c q1 N M H1 H2 H3`. Generalize the expression as in `hX12 : pa s ρ * pa s (fun i => ρ i + 1) = coord_mul_inv_coord_eq_one at hdv ⊢`. Establish `hXm : coord_mul_inv_coord_eq_one.Monic` using `by rw [← hX12]; exact (pa_monic _ _).mul (pa_monic _ _)`. Establish `hXd : coord_mul_inv_coord_eq_one.natDegree = 2 * s.card`. Rewrite using `[← hX12, Monic.natDegree_mul (pa_monic _ _) (pa_monic _ _), pa_natDegree, pa_natDegree]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hXn : coord_mul_inv_coord_eq_one.nextCoeff = ∑ i ∈ s, ρ i + ∑ i ∈ s, (ρ i + 1)`. Rewrite using `[← hX12, Monic.nextCoeff_mul (pa_monic _ _) (pa_monic _ _), pa_nextCoeff, pa_nextCoeff]`. Generalize the expression as in `hg : ((X + C 0) * (X + C e) : ℂ[X]) = g`. Establish `hgm : g.Monic` using `by rw [← hg]; exact (monic_X_add_C _).mul (monic_X_add_C _)`.

Establish `hgd : g.natDegree = 2`. Rewrite using `[← hg, Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]`. Establish `hgn : g.nextCoeff = e`. Rewrite using `[← hg, Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : (q1 - coord_mul_inv_coord_eq_one * g).natDegree ≤ 2 * s.card`. Apply `natDegree_sub_le_of_next _ _ _ hq1 (hXm.mul hgm) hdeg` to reduce the goal to its premises. Rewrite using `[Monic.natDegree_mul hXm hgm, hXd, hgd]`. Rewrite using `[Monic.nextCoeff_mul hXm hgm, hXn, hgn, he]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hR : (DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g)).natDegree ≤ 2 * s.card`. Establish `: DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) = C c * (q1 - coord_mul_inv_coord_eq_one * g) + ((∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) - (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1))))`. Unfold `DD`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Use `natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans h1) ((natDegree_sub_le_of_le ?_ ?_).trans (le_of_eq (max_self _)))` and prove the remaining obligations. Apply `natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `l hl`. Use `(natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)` and prove the remaining obligations. Rewrite using `[pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]`.

Use linear arithmetic over natural numbers and integers. Apply `natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `l hl`. Use `(natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)` and prove the remaining obligations. Rewrite using `[pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]`.

Use linear arithmetic over natural numbers and integers. Take `⟨S, hS⟩ : coord_mul_inv_coord_eq_one ∣ DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g)` from `dvd_sub hdv (Dvd.dvd.mul_left (dvd_mul_right _ _) _)`. Establish `hS0 : S.natDegree = 0`. Distinguish the cases in `h0 : S = 0`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Rewrite `hR` using `[hS, Monic.natDegree_mul' hXm h0, hXd]`. Use linear arithmetic over natural numbers and integers. Use `⟨S.coeff 0, ?_⟩` and prove the remaining obligations. Rewrite using `[← eq_C_of_natDegree_eq_zero hS0]`.

Take the linear combination `hS`.
-/
theorem DD_quot (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, DD s ρ c q1 N M = pa s ρ * pa s (fun i => ρ i + 1) *
      (C c * ((X + C 0) * (X + C e)) + C r) := by
  have hdv := DD_dvd s ρ hinj c q1 N M H1 H2 H3
  generalize hX12 : pa s ρ * pa s (fun i => ρ i + 1) = coord_mul_inv_coord_eq_one at hdv ⊢
  have hXm : coord_mul_inv_coord_eq_one.Monic := by rw [← hX12]; exact (pa_monic _ _).mul (pa_monic _ _)
  have hXd : coord_mul_inv_coord_eq_one.natDegree = 2 * s.card := by
    rw [← hX12, Monic.natDegree_mul (pa_monic _ _) (pa_monic _ _), pa_natDegree, pa_natDegree]; ring
  have hXn : coord_mul_inv_coord_eq_one.nextCoeff = ∑ i ∈ s, ρ i + ∑ i ∈ s, (ρ i + 1) := by
    rw [← hX12, Monic.nextCoeff_mul (pa_monic _ _) (pa_monic _ _), pa_nextCoeff, pa_nextCoeff]
  generalize hg : ((X + C 0) * (X + C e) : ℂ[X]) = g
  have hgm : g.Monic := by rw [← hg]; exact (monic_X_add_C _).mul (monic_X_add_C _)
  have hgd : g.natDegree = 2 := by
    rw [← hg, Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  have hgn : g.nextCoeff = e := by
    rw [← hg, Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]; ring
  have h1 : (q1 - coord_mul_inv_coord_eq_one * g).natDegree ≤ 2 * s.card := by
    apply natDegree_sub_le_of_next _ _ _ hq1 (hXm.mul hgm) hdeg
    · rw [Monic.natDegree_mul hXm hgm, hXd, hgd]
    · rw [Monic.nextCoeff_mul hXm hgm, hXn, hgn, he]; ring
  have hR : (DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g)).natDegree ≤ 2 * s.card := by
    have : DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) = C c * (q1 - coord_mul_inv_coord_eq_one * g) +
        ((∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) -
          (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1)))) := by
      unfold DD; ring
    rw [this]
    refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans h1) ((natDegree_sub_le_of_le ?_ ?_).trans (le_of_eq (max_self _)))
    · apply natDegree_sum_le_of_forall_le
      intro l hl
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      rw [pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]; omega
    · apply natDegree_sum_le_of_forall_le
      intro l hl
      refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
      rw [pa_natDegree, pa_natDegree, Finset.card_erase_of_mem hl]; omega
  obtain ⟨S, hS⟩ : coord_mul_inv_coord_eq_one ∣ DD s ρ c q1 N M - C c * (coord_mul_inv_coord_eq_one * g) :=
    dvd_sub hdv (Dvd.dvd.mul_left (dvd_mul_right _ _) _)
  have hS0 : S.natDegree = 0 := by
    by_cases h0 : S = 0
    · rw [h0]; simp
    · rw [hS, Monic.natDegree_mul' hXm h0, hXd] at hR; omega
  refine ⟨S.coeff 0, ?_⟩
  rw [← eq_C_of_natDegree_eq_zero hS0]
  linear_combination hS

/- English proof (translation)
Take `⟨r, hr⟩` from `DD_quot s ρ hinj c q1 N M H1 H2 H3 hq1 hdeg e he`. Use `⟨r, fun Y ha hb => ?_⟩` and prove the remaining obligations. Establish `hE` using `congrArg (eval Y) hr`. Rewrite `hE` using `[DD_eval]`. Simplify using `only [eval_mul, eval_add, eval_C, eval_X, pa_eval, add_zero] at hE`.

Establish `hA0 : (∏ i ∈ s, (Y + ρ i)) ≠ 0` using `Finset.prod_ne_zero_iff.2 ha`. Establish `hB0 : (∏ i ∈ s, (Y + (ρ i + 1))) ≠ 0` using `Finset.prod_ne_zero_iff.2 hb`. Establish `e1 : (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) = (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, M l * (Y + ρ l)⁻¹`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun l hl => ?_)` and prove the remaining obligations.

Rewrite using `[← Finset.mul_prod_erase s (fun i => Y + ρ i) hl]`. Establish `hinv` using `mul_inv_cancel₀ (ha l hl)`. Take the linear combination `(-(M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1))))) * hinv`. Establish `e2 : (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) = (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun l hl => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.mul_prod_erase s (fun i => Y + (ρ i + 1)) hl]`. Establish `hinv` using `mul_inv_cancel₀ (hb l hl)`. Take the linear combination `(-(N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1))))) * hinv`. Rewrite `hE` using `[e1, e2]`.

Generalize the expression as in `(∏ i ∈ s, (Y + ρ i)) = A at hE hA0 ⊢`. Generalize the expression as in `(∏ i ∈ s, (Y + (ρ i + 1))) = B at hE hB0 ⊢`. Establish `hAB : A * B * (A⁻¹ * B⁻¹) = 1`. Rewrite using `[mul_mul_mul_comm, mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0, mul_one]`. Establish `h5 : c * eval Y q1 = (c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) + (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹)) * (A * B)` using `by linear_combination hE`.

Rewrite using `[h5, mul_assoc, hAB, mul_one]`.
-/
theorem pf_abs (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1)
    (hq1 : q1.Monic) (hdeg : q1.natDegree = 2 * s.card + 2) (e : ℂ)
    (he : e = q1.nextCoeff - ∑ i ∈ s, ρ i - ∑ i ∈ s, (ρ i + 1)) :
    ∃ r : ℂ, ∀ Y : ℂ, (∀ i ∈ s, Y + ρ i ≠ 0) → (∀ i ∈ s, Y + (ρ i + 1) ≠ 0) →
      c * q1.eval Y * ((∏ i ∈ s, (Y + ρ i))⁻¹ * (∏ i ∈ s, (Y + (ρ i + 1)))⁻¹) =
        c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) + (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹) := by
  obtain ⟨r, hr⟩ := DD_quot s ρ hinj c q1 N M H1 H2 H3 hq1 hdeg e he
  refine ⟨r, fun Y ha hb => ?_⟩
  have hE := congrArg (eval Y) hr
  rw [DD_eval] at hE
  simp only [eval_mul, eval_add, eval_C, eval_X, pa_eval, add_zero] at hE
  have hA0 : (∏ i ∈ s, (Y + ρ i)) ≠ 0 := Finset.prod_ne_zero_iff.2 ha
  have hB0 : (∏ i ∈ s, (Y + (ρ i + 1))) ≠ 0 := Finset.prod_ne_zero_iff.2 hb
  have e1 : (∑ l ∈ s, M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1)))) =
      (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, M l * (Y + ρ l)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Finset.mul_prod_erase s (fun i => Y + ρ i) hl]
    have hinv := mul_inv_cancel₀ (ha l hl)
    linear_combination (-(M l * ((∏ j ∈ s.erase l, (Y + ρ j)) * ∏ j ∈ s, (Y + (ρ j + 1))))) * hinv
  have e2 : (∑ l ∈ s, N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1)))) =
      (∏ i ∈ s, (Y + ρ i)) * (∏ i ∈ s, (Y + (ρ i + 1))) * ∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [← Finset.mul_prod_erase s (fun i => Y + (ρ i + 1)) hl]
    have hinv := mul_inv_cancel₀ (hb l hl)
    linear_combination (-(N l * ((∏ j ∈ s, (Y + ρ j)) * ∏ j ∈ s.erase l, (Y + (ρ j + 1))))) * hinv
  rw [e1, e2] at hE
  generalize (∏ i ∈ s, (Y + ρ i)) = A at hE hA0 ⊢
  generalize (∏ i ∈ s, (Y + (ρ i + 1))) = B at hE hB0 ⊢
  have hAB : A * B * (A⁻¹ * B⁻¹) = 1 := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hA0, mul_inv_cancel₀ hB0, mul_one]
  have h5 : c * eval Y q1 = (c * (Y * (Y + e)) + r - (∑ l ∈ s, M l * (Y + ρ l)⁻¹) +
      (∑ l ∈ s, N l * (Y + (ρ l + 1))⁻¹)) * (A * B) := by linear_combination hE
  rw [h5, mul_assoc, hAB, mul_one]

def q1P (P : Par) : ℂ[X] :=
  ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))

/- English proof (translation)
The claim follows from `monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))`.
-/
theorem q_polynomial_monic (P : Par) : (q1P P).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))

/- English proof (translation)
Unfold `q1P`. Rewrite using `[natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]`. Establish `: ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2`. Introduce `i _`. Rewrite using `[Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]`.

Rewrite using `[Finset.sum_congr rfl this]`. Simplify using `[mul_comm]`.
-/
theorem natDegree_q1_polynomial (P : Par) : (q1P P).natDegree = 2 * P.k := by
  unfold q1P
  rw [natDegree_prod_of_monic _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  have : ∀ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))).natDegree = 2 := by
    intro i _
    rw [Monic.natDegree_mul (monic_X_add_C _) (monic_X_add_C _), natDegree_X_add_C, natDegree_X_add_C]
  rw [Finset.sum_congr rfl this]
  simp [mul_comm]

/- English proof (translation)
Unfold `q1P`. Rewrite using `[Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]`.
-/
theorem q_polynomial_next_coeff (P : Par) :
    (q1P P).nextCoeff = ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) := by
  unfold q1P
  rw [Monic.nextCoeff_prod _ _ (fun _ _ => (monic_X_add_C _).mul (monic_X_add_C _))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Monic.nextCoeff_mul (monic_X_add_C _) (monic_X_add_C _), nextCoeff_X_add_C, nextCoeff_X_add_C]

/- English proof (translation)
Unfold `qC q1P`. Simplify using `only [eval_prod, eval_mul, eval_add, eval_X, eval_C]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl (fun i _ => by ring)`.
-/
theorem qC_eq (P : Par) (Y : ℂ) : qC P Y = -((P.T : ℂ) * P.T') * (q1P P).eval Y := by
  unfold qC q1P
  simp only [eval_prod, eval_mul, eval_add, eval_X, eval_C]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => by ring)

/- English proof (translation)
Establish `hl'` using `Finset.mem_Icc.1 hl`. Distinguish the cases in `h : ∃ π', Up P l π' π`. Take `⟨π', hU⟩` from `h`. Establish `hp` using `(Mx3.nrmFacts P hP l hl π').1 π hU`. Establish `hpos : 0 < NrmDown P l π` using `by rw [hp.2]; exact hp.1`.

Establish `hD : ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) * ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) ≠ 0`. Introduce `h0`. Unfold `NrmDown at hpos`. Rewrite `hpos` using `[h0, div_zero]`. Conclude with `lt_irrefl _ hpos`.

Unfold `NrmDown`. Conclude with `div_mul_cancel₀ _ hD`. Rewrite using `[(Mx3.nrmFacts P hP l hl π).2.2 h]`. Establish `ht` using `Mx3.bot P l hl π h`. Establish `h0 : I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) = 0`.

Unfold `I.qpoly`. Establish `: ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0`. Apply `Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)` to reduce the goal to its premises. Rewrite using `[ht]`. Unfold `Par.lo`.

Apply the tactic sequence `rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Rewrite using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem nrmDown_key (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) =
      -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) := by
  have hl' := Finset.mem_Icc.1 hl
  by_cases h : ∃ π', Up P l π' π
  · obtain ⟨π', hU⟩ := h
    have hp := (Mx3.nrmFacts P hP l hl π').1 π hU
    have hpos : 0 < NrmDown P l π := by rw [hp.2]; exact hp.1
    have hD : ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) ≠ 0 := by
      intro h0
      unfold NrmDown at hpos
      rw [h0, div_zero] at hpos
      exact lt_irrefl _ hpos
    unfold NrmDown
    exact div_mul_cancel₀ _ hD
  · rw [(Mx3.nrmFacts P hP l hl π).2.2 h]
    have ht := Mx3.bot P l hl π h
    have h0 : I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) = 0 := by
      unfold I.qpoly
      have : ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0 := by
        apply Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        rw [ht]; unfold Par.lo
        rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring
      rw [this]; simp
    rw [h0]; simp

/- English proof (translation)
Introduce `i hi j hj h`. Establish `h2 : rho P π i = rho P π j` using `by exact_mod_cast h`. Break down `lt_trichotomy i j with h1 | h1 | h1` into its components or cases. Conclude with `absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h1))`. Conclude with `h1`.

Conclude with `absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h1))`.
-/
theorem rhoC_inj (P : Par) (hP : P.OK) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1),
    (rho P π i : ℂ) = (rho P π j : ℂ) → i = j := by
  intro i hi j hj h
  have h2 : rho P π i = rho P π j := by exact_mod_cast h
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h1))
  · exact h1
  · exact absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h1))

/- English proof (translation)
Introduce `l hl`. Establish `hk` using `congrArg (fun x : ℝ => (x : ℂ)) (nrmDown_key P hP l hl π)`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_one] at hk`. Establish `hq` using `(Mx3.realPoints P π (-rho P π l)).2`. Rewrite `hq` using `[Complex.ofReal_neg]`.

Rewrite using `[← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]`. Establish `e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + (rho P π j : ℂ)) = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Establish `e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + ((rho P π j : ℂ) + 1)) = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l + 1)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Rewrite using `[e1, e2]`. Take the linear combination `hk`.
-/
theorem moduleH1Alt (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1),
    -((P.T : ℂ) * P.T') * (q1P P).eval (-(rho P π l : ℂ)) + (NrmDown P l π : ℂ) *
      ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + (rho P π j : ℂ))) *
        ∏ j ∈ Icc 1 (P.k - 1), (-(rho P π l : ℂ) + ((rho P π j : ℂ) + 1))) = 0 := by
  intro l hl
  have hk := congrArg (fun x : ℝ => (x : ℂ)) (nrmDown_key P hP l hl π)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_add,
    Complex.ofReal_neg, Complex.ofReal_one] at hk
  have hq := (Mx3.realPoints P π (-rho P π l)).2
  rw [Complex.ofReal_neg] at hq
  rw [← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + (rho P π j : ℂ)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-(rho P π l : ℂ) + ((rho P π j : ℂ) + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l + 1) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e1, e2]
  linear_combination hk

/- English proof (translation)
Introduce `l hl`. Establish `hk` using `congrArg (fun x : ℝ => (x : ℂ)) (Mx3.nrm_key P hP l hl π)`. Simplify using `only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_one] at hk`. Establish `hq` using `(Mx3.realPoints P π (-rho P π l - 1)).2`. Establish `e0 : ((-rho P π l - 1 : ℝ) : ℂ) = -((rho P π l : ℂ) + 1)` using `by push_cast; ring`.

Rewrite `hq` using `[e0]`. Rewrite using `[← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]`. Establish `e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ)) = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Establish `e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) = ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l)` using `Finset.prod_congr rfl (fun j _ => by ring)`. Rewrite using `[e1, e2]`.

Take the linear combination `hk`.
-/
theorem residue_quadratic_identity (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1),
    -((P.T : ℂ) * P.T') * (q1P P).eval (-((rho P π l : ℂ) + 1)) - (Nrm P l π : ℂ) *
      ((∏ j ∈ Icc 1 (P.k - 1), (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ))) *
        ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1))) = 0 := by
  intro l hl
  have hk := congrArg (fun x : ℝ => (x : ℂ)) (Mx3.nrm_key P hP l hl π)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_sub,
    Complex.ofReal_neg, Complex.ofReal_one] at hk
  have hq := (Mx3.realPoints P π (-rho P π l - 1)).2
  have e0 : ((-rho P π l - 1 : ℝ) : ℂ) = -((rho P π l : ℂ) + 1) := by push_cast; ring
  rw [e0] at hq
  rw [← qC_eq, hq, ← Finset.mul_prod_erase _ _ hl]
  have e1 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + (rho P π j : ℂ)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l - 1) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  have e2 : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (-((rho P π l : ℂ) + 1) + ((rho P π j : ℂ) + 1)) =
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, ((rho P π j : ℂ) - rho P π l) :=
    Finset.prod_congr rfl (fun j _ => by ring)
  rw [e1, e2]
  linear_combination hk

/- English proof (translation)
Introduce `l hl m hm h`. Establish `hl'` using `Finset.mem_Icc.1 hl`. Establish `hr : rho P π m = rho P π l + 1` using `by exact_mod_cast h`. Establish `hml : m < l`. Break down `lt_trichotomy m l with h1 | h1 | h1` into its components or cases.

Conclude with `h1`. Rewrite `hr` using `[h1]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Mx3.rho_inj P hP π l m hl hm h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) = 0` using `Finset.prod_eq_zero (i := m) (Finset.mem_erase.2 ⟨ne_of_lt hml, hm⟩) (by rw [hr]; ring)`. Unfold `Nrm`. Rewrite using `[this, mul_zero, div_zero, Complex.ofReal_zero]`. Establish `: ∏ j ∈ (Icc 1 (P.k - 1)).erase m, (rho P π j - rho P π m + 1) = 0` using `Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨ne_of_gt hml, hl⟩) (by rw [hr]; ring)`.

Unfold `NrmDown`. Rewrite using `[this, zero_mul, div_zero, Complex.ofReal_zero]`. Establish `hI` using `Mx3.tyInterlaces P hP π`. Establish `o3` using `(Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.1 m hm hml`. Establish `b` using `hI l hl`.

Establish `hu : P.u l = rho P π l + 1 / 2` using `by linarith [o3.1, b.1]`. Establish `hu' : P.u' l = rho P π l + 1 / 2` using `by linarith [o3.2, b.2.1]`. Establish `hd : (X + C (1 / 2 + (P.u l : ℂ))) * (X + C (1 / 2 + (P.u' l : ℂ))) ∣ q1P P` using `Finset.dvd_prod_of_mem (fun i => (X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ)))) (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)`. Establish `e1 : (1 / 2 + (P.u l : ℂ)) = (rho P π l : ℂ) + 1` using `by rw [hu]; push_cast; ring`. Establish `e2 : (1 / 2 + (P.u' l : ℂ)) = (rho P π l : ℂ) + 1` using `by rw [hu']; push_cast; ring`.

Rewrite `hd` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem double_root_of_adjacent_rho (P : Par) (hP : P.OK) (π : Ty P) : ∀ l ∈ Icc 1 (P.k - 1), ∀ m ∈ Icc 1 (P.k - 1),
    (rho P π m : ℂ) = (rho P π l : ℂ) + 1 → (Nrm P l π : ℂ) = 0 ∧ (NrmDown P m π : ℂ) = 0 ∧
      (X + C ((rho P π l : ℂ) + 1)) * (X + C ((rho P π l : ℂ) + 1)) ∣ q1P P := by
  intro l hl m hm h
  have hl' := Finset.mem_Icc.1 hl
  have hr : rho P π m = rho P π l + 1 := by exact_mod_cast h
  have hml : m < l := by
    rcases lt_trichotomy m l with h1 | h1 | h1
    · exact h1
    · rw [h1] at hr; linarith
    · have := Mx3.rho_inj P hP π l m hl hm h1; linarith
  refine ⟨?_, ?_, ?_⟩
  · have : ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l - 1) = 0 :=
      Finset.prod_eq_zero (i := m) (Finset.mem_erase.2 ⟨ne_of_lt hml, hm⟩) (by rw [hr]; ring)
    unfold Nrm
    rw [this, mul_zero, div_zero, Complex.ofReal_zero]
  · have : ∏ j ∈ (Icc 1 (P.k - 1)).erase m, (rho P π j - rho P π m + 1) = 0 :=
      Finset.prod_eq_zero (i := l) (Finset.mem_erase.2 ⟨ne_of_gt hml, hl⟩) (by rw [hr]; ring)
    unfold NrmDown
    rw [this, zero_mul, div_zero, Complex.ofReal_zero]
  · have hI := Mx3.tyInterlaces P hP π
    have o3 := (Mx3.ord P.k P.u P.u' (rho P π) hI l hl).2.2.1 m hm hml
    have b := hI l hl
    have hu : P.u l = rho P π l + 1 / 2 := by linarith [o3.1, b.1]
    have hu' : P.u' l = rho P π l + 1 / 2 := by linarith [o3.2, b.2.1]
    have hd : (X + C (1 / 2 + (P.u l : ℂ))) * (X + C (1 / 2 + (P.u' l : ℂ))) ∣ q1P P :=
      Finset.dvd_prod_of_mem (fun i => (X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))
        (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
    have e1 : (1 / 2 + (P.u l : ℂ)) = (rho P π l : ℂ) + 1 := by rw [hu]; push_cast; ring
    have e2 : (1 / 2 + (P.u' l : ℂ)) = (rho P π l : ℂ) + 1 := by rw [hu']; push_cast; ring
    rwa [e1, e2] at hd

/- English proof (translation)
Rewrite using `[q_polynomial_next_coeff]`. Establish `s1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) = (P.k : ℂ) + ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ))`. Rewrite using `[Finset.sum_congr rfl (fun i _ => show ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) = 1 + ((P.u i : ℂ) + (P.u' i : ℂ)) by ring), Finset.sum_add_distrib]`. Simplify using the standard rewrite rules. Establish `s2 : ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) = (∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ)) + ((P.k : ℂ) - 1)`.

Rewrite using `[Finset.sum_add_distrib]`. Simplify using `[Nat.cast_sub hP.k_pos]`. Rewrite using `[s1, s2]`. Unfold `aC`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem modE (P : Par) (hP : P.OK) (π : Ty P) :
    2 * (aC P π : ℂ) + 1 = (q1P P).nextCoeff - ∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ) -
      ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) := by
  rw [q_polynomial_next_coeff]
  have s1 : ∑ i ∈ Icc 1 P.k, ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      (P.k : ℂ) + ∑ i ∈ Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ)) := by
    rw [Finset.sum_congr rfl (fun i _ => show ((1 / 2 + (P.u i : ℂ)) + (1 / 2 + (P.u' i : ℂ))) =
      1 + ((P.u i : ℂ) + (P.u' i : ℂ)) by ring), Finset.sum_add_distrib]
    simp
  have s2 : ∑ i ∈ Icc 1 (P.k - 1), ((rho P π i : ℂ) + 1) =
      (∑ i ∈ Icc 1 (P.k - 1), (rho P π i : ℂ)) + ((P.k : ℂ) - 1) := by
    rw [Finset.sum_add_distrib]
    simp [Nat.cast_sub hP.k_pos]
  rw [s1, s2]
  unfold aC
  push_cast
  ring

/- English proof (translation)
Take `⟨r, hr⟩` from `pf_abs (Icc 1 (P.k - 1)) (fun i => (rho P π i : ℂ)) (rhoC_inj P hP π) (-((P.T : ℂ) * P.T')) (q1P P) (fun l => (Nrm P l π : ℂ)) (fun l => (NrmDown P l π : ℂ)) (moduleH1Alt P hP π) (residue_quadratic_identity P hP π) (double_root_of_adjacent_rho P hP π) (q_polynomial_monic P) (by r …`. Establish `f0 : ∀ i ∈ Icc 1 (P.k - 1), u - 1 + (rho P π i : ℂ) ≠ 0` using `Finset.prod_ne_zero_iff.1 h0`. Establish `f1 : ∀ i ∈ Icc 1 (P.k - 1), u + (rho P π i : ℂ) ≠ 0` using `Finset.prod_ne_zero_iff.1 h1`. Establish `f2 : ∀ i ∈ Icc 1 (P.k - 1), u + 1 + (rho P π i : ℂ) ≠ 0` using `Finset.prod_ne_zero_iff.1 h2`. Establish `E0` using `hr (u - 1) f0 (fun i hi h => f1 i hi (by linear_combination h))`.

Establish `E1` using `hr u f1 (fun i hi h => f2 i hi (by linear_combination h))`. Establish `p0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + ((rho P π i : ℂ) + 1)) = xC P π u` using `Finset.prod_congr rfl (fun i _ => by ring)`. Establish `p1 : ∏ i ∈ Icc 1 (P.k - 1), (u + ((rho P π i : ℂ) + 1)) = xC P π (u + 1)` using `Finset.prod_congr rfl (fun i _ => by ring)`. Establish `x0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + (rho P π i : ℂ)) = xC P π (u - 1)` using `rfl`. Establish `x1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rho P π i : ℂ)) = xC P π u` using `rfl`.

Rewrite `E0` using `[p0, x0, ← qC_eq]`. Rewrite `E1` using `[p1, x1, ← qC_eq]`. Rewrite using `[E0, E1]`. Establish `T : ∀ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) - (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) = -((NrmDown P l π : ℂ) * (u - 1 + (rho P π l : ℂ))⁻¹) + (Nrm P l π : ℂ) * (u - 1 + ((rho P π l : ℂ) + 1))⁻¹ + (NrmDown P …`. Introduce `l hl`.

Rewrite using `[show u - 1 + ((rho P π l : ℂ) + 1) = u + rho P π l by ring, show u + ((rho P π l : ℂ) + 1) = u + rho P π l + 1 by ring, show u - 1 + (rho P π l : ℂ) = u + rho P π l - 1 by ring]`. Establish `hx` using `mul_inv_cancel₀ (f1 l hl)`. Establish `hy : (u + rho P π l + 1) * (u + rho P π l + 1)⁻¹ = 1` using `mul_inv_cancel₀ (fun h => f2 l hl (by linear_combination h))`. Establish `hz : (u + rho P π l - 1) * (u + rho P π l - 1)⁻¹ = 1` using `mul_inv_cancel₀ (fun h => f0 l hl (by linear_combination h))`. Establish `hxy : (u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹ = (u + rho P π l)⁻¹ - (u + rho P π l + 1)⁻¹`.

Take the linear combination `(-(u + rho P π l + 1)⁻¹) * hx + (u + rho P π l)⁻¹ * hy`. Establish `hxz : (u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹ = (u + rho P π l - 1)⁻¹ - (u + rho P π l)⁻¹`. Take the linear combination `(u + rho P π l - 1)⁻¹ * hx - (u + rho P π l)⁻¹ * hz`. Take the linear combination `(Nrm P l π : ℂ) * hxy - (NrmDown P l π : ℂ) * hxz`. Rewrite using `[Finset.sum_congr rfl T, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]`.

Establish `hTT : (P.TT : ℂ) = (P.T : ℂ) * P.T'` using `by unfold Par.TT; push_cast; ring`. Rewrite using `[hTT]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pf (P : Par) (hP : P.OK) (π : Ty P) (u : ℂ) (h0 : xC P π (u - 1) ≠ 0) (h1 : xC P π u ≠ 0)
    (h2 : xC P π (u + 1) ≠ 0) :
    qC P (u - 1) * ((xC P π (u - 1))⁻¹ * (xC P π u)⁻¹) - qC P u * ((xC P π u)⁻¹ * (xC P π (u + 1))⁻¹) =
      (2 * (aC P π : ℂ) + 2 * u) * (P.TT : ℂ) + ∑ l ∈ Icc 1 (P.k - 1),
        ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by
  obtain ⟨r, hr⟩ := pf_abs (Icc 1 (P.k - 1)) (fun i => (rho P π i : ℂ)) (rhoC_inj P hP π)
    (-((P.T : ℂ) * P.T')) (q1P P) (fun l => (Nrm P l π : ℂ)) (fun l => (NrmDown P l π : ℂ))
    (moduleH1Alt P hP π) (residue_quadratic_identity P hP π) (double_root_of_adjacent_rho P hP π) (q_polynomial_monic P)
    (by rw [natDegree_q1_polynomial, Nat.card_Icc]; have := hP.k_pos; omega) (2 * (aC P π : ℂ) + 1) (modE P hP π)
  have f0 : ∀ i ∈ Icc 1 (P.k - 1), u - 1 + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h0
  have f1 : ∀ i ∈ Icc 1 (P.k - 1), u + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h1
  have f2 : ∀ i ∈ Icc 1 (P.k - 1), u + 1 + (rho P π i : ℂ) ≠ 0 := Finset.prod_ne_zero_iff.1 h2
  have E0 := hr (u - 1) f0 (fun i hi h => f1 i hi (by linear_combination h))
  have E1 := hr u f1 (fun i hi h => f2 i hi (by linear_combination h))
  have p0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + ((rho P π i : ℂ) + 1)) = xC P π u :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have p1 : ∏ i ∈ Icc 1 (P.k - 1), (u + ((rho P π i : ℂ) + 1)) = xC P π (u + 1) :=
    Finset.prod_congr rfl (fun i _ => by ring)
  have x0 : ∏ i ∈ Icc 1 (P.k - 1), (u - 1 + (rho P π i : ℂ)) = xC P π (u - 1) := rfl
  have x1 : ∏ i ∈ Icc 1 (P.k - 1), (u + (rho P π i : ℂ)) = xC P π u := rfl
  rw [p0, x0, ← qC_eq] at E0
  rw [p1, x1, ← qC_eq] at E1
  rw [E0, E1]
  have T : ∀ l ∈ Icc 1 (P.k - 1),
      ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
          (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) =
      -((NrmDown P l π : ℂ) * (u - 1 + (rho P π l : ℂ))⁻¹) + (Nrm P l π : ℂ) * (u - 1 + ((rho P π l : ℂ) + 1))⁻¹ +
        (NrmDown P l π : ℂ) * (u + (rho P π l : ℂ))⁻¹ - (Nrm P l π : ℂ) * (u + ((rho P π l : ℂ) + 1))⁻¹ := by
    intro l hl
    rw [show u - 1 + ((rho P π l : ℂ) + 1) = u + rho P π l by ring,
      show u + ((rho P π l : ℂ) + 1) = u + rho P π l + 1 by ring,
      show u - 1 + (rho P π l : ℂ) = u + rho P π l - 1 by ring]
    have hx := mul_inv_cancel₀ (f1 l hl)
    have hy : (u + rho P π l + 1) * (u + rho P π l + 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h => f2 l hl (by linear_combination h))
    have hz : (u + rho P π l - 1) * (u + rho P π l - 1)⁻¹ = 1 :=
      mul_inv_cancel₀ (fun h => f0 l hl (by linear_combination h))
    have hxy : (u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹ = (u + rho P π l)⁻¹ - (u + rho P π l + 1)⁻¹ := by
      linear_combination (-(u + rho P π l + 1)⁻¹) * hx + (u + rho P π l)⁻¹ * hy
    have hxz : (u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹ = (u + rho P π l - 1)⁻¹ - (u + rho P π l)⁻¹ := by
      linear_combination (u + rho P π l - 1)⁻¹ * hx - (u + rho P π l)⁻¹ * hz
    linear_combination (Nrm P l π : ℂ) * hxy - (NrmDown P l π : ℂ) * hxz
  rw [Finset.sum_congr rfl T, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have hTT : (P.TT : ℂ) = (P.T : ℂ) * P.T' := by unfold Par.TT; push_cast; ring
  rw [hTT]
  ring

end

end PartF

section PartA

open  Formalism.FourierDecayAlt Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

section Poly

variable {B : Type} [Ring B] [Algebra ℂ B]

noncomputable def ev (Y : ℂ) : B[X] →+* B :=
  eval₂RingHom' (RingHom.id B) (algebraMap ℂ B Y) (fun a => (Algebra.commutes Y a).symm)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_apply (Y : ℂ) (p : B[X]) : ev Y p = eval₂ (RingHom.id B) (algebraMap ℂ B Y) p := rfl

/- English proof (translation)
Rewrite using `[ev_apply, eval₂_C]`. Both sides reduce to the same expression.
-/
theorem ev_C (Y : ℂ) (a : B) : ev Y (C a) = a := by rw [ev_apply, eval₂_C]; rfl

/- English proof (translation)
Rewrite using `[ev_apply, eval₂_X]`.
-/
theorem ev_X (Y : ℂ) : ev Y (X : B[X]) = algebraMap ℂ B Y := by rw [ev_apply, eval₂_X]

/- English proof (translation)
Rewrite using `[ev_apply, eval₂_monomial]`. Both sides reduce to the same expression.
-/
theorem ev_monomial (Y : ℂ) (n : ℕ) (a : B) : ev Y (monomial n a) = a * algebraMap ℂ B Y ^ n := by
  rw [ev_apply, eval₂_monomial]; rfl

/- English proof (translation)
Rewrite using `[ev_apply, eval₂_eq_sum, Polynomial.sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]`.
-/
theorem ev_eq_sum (Y : ℂ) (p : B[X]) : ev Y p = ∑ i ∈ p.support, Y ^ i • p.coeff i := by
  rw [ev_apply, eval₂_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, Algebra.smul_def]

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [add_comp, map_add, map_add, hp, hq]`. Consider the case `monomial n a => rw [monomial_comp, map_mul, map_pow, map_add, ev_C, ev_X, ev_C, ev_monomial, map_add]`.
-/
theorem ev_comp (Y c : ℂ) (p : B[X]) : ev Y (p.comp (X + C (algebraMap ℂ B c))) = ev (Y + c) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, map_add, hp, hq]
  | monomial n a => rw [monomial_comp, map_mul, map_pow, map_add, ev_C, ev_X, ev_C, ev_monomial, map_add]

def IsPoly (F : ℂ → B) : Prop := ∃ p : B[X], ∀ Y, F Y = ev Y p

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Conclude with `⟨p, fun Y => by rw [h, hp]⟩`.
-/
theorem IsPoly.congr {F G : ℂ → B} (hF : IsPoly F) (h : ∀ Y, G Y = F Y) : IsPoly G := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p, fun Y => by rw [h, hp]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨C a, fun Y => (ev_C Y a).symm⟩`.
-/
theorem IsPoly.const (a : B) : IsPoly (fun _ => a) := ⟨C a, fun Y => (ev_C Y a).symm⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Take `⟨q, hq⟩` from `hG`. Conclude with `⟨p + q, fun Y => by show F Y + G Y = _; rw [map_add, hp, hq]⟩`.
-/
theorem IsPoly.add {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y + G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p + q, fun Y => by show F Y + G Y = _; rw [map_add, hp, hq]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Take `⟨q, hq⟩` from `hG`. Conclude with `⟨p - q, fun Y => by show F Y - G Y = _; rw [map_sub, hp, hq]⟩`.
-/
theorem IsPoly.sub {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y - G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p - q, fun Y => by show F Y - G Y = _; rw [map_sub, hp, hq]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Conclude with `⟨-p, fun Y => by show -F Y = _; rw [map_neg, hp]⟩`.
-/
theorem IsPoly.neg {F : ℂ → B} (hF : IsPoly F) : IsPoly (fun Y => -F Y) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨-p, fun Y => by show -F Y = _; rw [map_neg, hp]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Take `⟨q, hq⟩` from `hG`. Conclude with `⟨p * q, fun Y => by show F Y * G Y = _; rw [map_mul, hp, hq]⟩`.
-/
theorem IsPoly.mul {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) : IsPoly (fun Y => F Y * G Y) := by
  obtain ⟨p, hp⟩ := hF; obtain ⟨q, hq⟩ := hG
  exact ⟨p * q, fun Y => by show F Y * G Y = _; rw [map_mul, hp, hq]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using IsPoly.const (0 : B)`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem IsPoly.sum {ι : Type} (s : Finset ι) (F : ι → ℂ → B) (h : ∀ i ∈ s, IsPoly (F i)) :
    IsPoly (fun Y => ∑ i ∈ s, F i Y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsPoly.const (0 : B)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Assemble the required witnesses or components as `⟨p.map (algebraMap ℂ B), fun Y => by rw [ev_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply]⟩`.
-/
theorem IsPoly.scalar (p : ℂ[X]) : IsPoly (fun Y => algebraMap ℂ B (p.eval Y)) :=
  ⟨p.map (algebraMap ℂ B), fun Y => by rw [ev_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Conclude with `⟨p.comp (X + C (algebraMap ℂ B c)), fun Y => by show F (Y + c) = _; rw [ev_comp, hp]⟩`.
-/
theorem IsPoly.shift {F : ℂ → B} (hF : IsPoly F) (c : ℂ) : IsPoly (fun Y => F (Y + c)) := by
  obtain ⟨p, hp⟩ := hF
  exact ⟨p.comp (X + C (algebraMap ℂ B c)), fun Y => by show F (Y + c) = _; rw [ev_comp, hp]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hF`. Rewrite using `[← Module.forall_dual_apply_eq_zero_iff ℂ]`. Introduce `φ`. Establish `hev : ∀ Z, φ (F Z) = (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]).eval Z`. Introduce `Z`.

Rewrite using `[hp, ev_eq_sum, map_sum, eval_finsetSum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, eval_monomial, smul_eq_mul, mul_comm]`. Establish `h0 : (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]) = 0`. Apply `eq_zero_of_infinite_isRoot` to reduce the goal to its premises.

Use `hS.infinite_compl.mono ?_` and prove the remaining obligations. Introduce `Z hZ`. Use `show eval Z _ = 0`. Rewrite using `[← hev, h Z hZ, map_zero]`. Rewrite using `[hev, h0, eval_zero]`.
-/
theorem IsPoly.eq_zero {F : ℂ → B} (hF : IsPoly F) {S : Set ℂ} (hS : S.Finite) (h : ∀ Y, Y ∉ S → F Y = 0)
    (Y : ℂ) : F Y = 0 := by
  obtain ⟨p, hp⟩ := hF
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hev : ∀ Z, φ (F Z) = (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]).eval Z := by
    intro Z
    rw [hp, ev_eq_sum, map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, eval_monomial, smul_eq_mul, mul_comm]
  have h0 : (∑ i ∈ p.support, monomial i (φ (p.coeff i)) : ℂ[X]) = 0 := by
    apply eq_zero_of_infinite_isRoot
    refine hS.infinite_compl.mono ?_
    intro Z hZ
    show eval Z _ = 0
    rw [← hev, h Z hZ, map_zero]
  rw [hev, h0, eval_zero]

/- English proof (translation)
The claim follows from `sub_eq_zero.1 ((hF.sub hG).eq_zero hS (fun Z hZ => sub_eq_zero.2 (h Z hZ)) Y)`.
-/
theorem IsPoly.ext {F G : ℂ → B} (hF : IsPoly F) (hG : IsPoly G) {S : Set ℂ} (hS : S.Finite)
    (h : ∀ Y, Y ∉ S → F Y = G Y) (Y : ℂ) : F Y = G Y :=
  sub_eq_zero.1 ((hF.sub hG).eq_zero hS (fun Z hZ => sub_eq_zero.2 (h Z hZ)) Y)

end Poly

section AbsDet

variable {B : Type} [Ring B] [Algebra ℂ B]

/- English proof (translation)
Establish `T5 : τ1 * (i0 * i1) = i0` using `by rw [hi, ← mul_assoc, h11, one_mul]`. Establish `FreeQuotientRank : τ1 * (i1 * i2) = i2` using `by rw [← mul_assoc, h11, one_mul]`. Establish `K : τ1 * (m1 * l1 - l1 * m1) = q0 • i0 - q1 • i2`. Rewrite using `[Y3, mul_sub, mul_smul_comm, mul_smul_comm, T5, FreeQuotientRank]`. Establish `e2 : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0`.

Establish `s : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = q1 • (i2 * τ0) + τ1 * (m1 * l1 - l1 * m1) * τ0`. Rewrite using `[← Y1']`. Simplify using `only [add_mul, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[s, K, sub_mul, smul_mul_assoc, smul_mul_assoc, h00', Algebra.algebraMap_eq_smul_one]`.

Normalize the expressions using the abelian group laws. Establish `F1 : τ1 * l1 * i1 = l0` using `by rw [← Y1, mul_assoc, h11, mul_one]`. Establish `F2 : τ0 * m0 * i0 = m1` using `by rw [← Y1', mul_assoc, h00, mul_one]`. Use `⟨?_, e2, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `s : (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) = ((q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0)) * l0 - q0 • (τ1 * l1 * i1)`.

Simplify using `only [mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[s, e2, F1, ← Algebra.smul_def, sub_self]`. Establish `s : τ1 * m1 * (τ0 * l0) = τ1 * (τ0 * m0 * l0)`. Rewrite using `[mul_assoc τ1, ← mul_assoc m1, Y1']`.

Rewrite using `[s, mul_add, mul_smul_comm, h11, Algebra.algebraMap_eq_smul_one]`. Normalize the expressions using the abelian group laws. Rewrite using `[mul_assoc, Y1', sub_self]`. Establish `s : (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) = q0 • (i1 * τ1 * m1) - τ0 * m0 * (τ1 * (m1 * l1 - l1 * m1)) - q1 • (τ0 * m0 * i2)`. Establish `s2 : τ0 * m0 * l0 * (τ1 * m1) = τ0 * m0 * (τ1 * (l1 * m1))`.

Rewrite using `[mul_assoc (τ0 * m0), ← mul_assoc l0, Y1, mul_assoc τ1]`. Rewrite using `[add_mul, s2]`. Simplify using `only [mul_add, mul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[s, K, h11', one_mul, mul_sub, mul_smul_comm, mul_smul_comm, F2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[add_mul, smul_mul_assoc, h11', mul_assoc (τ0 * m0) l0 τ1, Y1, Algebra.algebraMap_eq_smul_one]`. Normalize the expressions using the abelian group laws. Establish `s : τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) = -(τ0 * (τ1 * (m1 * l1 - l1 * m1))) - q1 • (τ0 * i2)`. Establish `s2 : τ0 * l0 * (τ1 * m1) = τ0 * (τ1 * (l1 * m1))`.

Rewrite using `[mul_assoc τ0, ← mul_assoc l0, Y1, mul_assoc]`. Rewrite using `[s2]`. Simplify using `only [mul_add, mul_sub, mul_smul_comm, mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[s, K, mul_sub, mul_smul_comm, mul_smul_comm, h00, Algebra.algebraMap_eq_smul_one]`.

Normalize the expressions using the abelian group laws. Rewrite using `[mul_assoc, Y1, sub_self]`.
-/
theorem det_abs (τ0 τ1 i0 i1 i2 l0 l1 m0 m1 : B) (q0 q1 : ℂ)
    (h00 : τ0 * i0 = 1) (h00' : i0 * τ0 = 1) (h11 : τ1 * i1 = 1) (h11' : i1 * τ1 = 1)
    (hi : i0 * i1 = i1 * i0)
    (Y1 : l0 * τ1 = τ1 * l1) (Y1' : m1 * τ0 = τ0 * m0)
    (Y3 : m1 * l1 - l1 * m1 = q0 • (i0 * i1) - q1 • (i1 * i2)) :
    (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) = 0 ∧
    (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0 ∧
    τ1 * m1 * (τ0 * l0) - τ1 * (q0 • i1 + τ0 * m0 * l0) = -algebraMap ℂ B q0 ∧
    τ1 * m1 * τ0 - τ1 * (τ0 * m0) = 0 ∧
    (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) = 0 ∧
    (q0 • i1 + τ0 * m0 * l0) * τ1 - τ0 * m0 * (τ1 * l1) = algebraMap ℂ B q0 ∧
    τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) = -algebraMap ℂ B q0 ∧
    τ0 * l0 * τ1 - τ0 * (τ1 * l1) = 0 := by
  have T5 : τ1 * (i0 * i1) = i0 := by rw [hi, ← mul_assoc, h11, one_mul]
  have FreeQuotientRank : τ1 * (i1 * i2) = i2 := by rw [← mul_assoc, h11, one_mul]
  have K : τ1 * (m1 * l1 - l1 * m1) = q0 • i0 - q1 • i2 := by
    rw [Y3, mul_sub, mul_smul_comm, mul_smul_comm, T5, FreeQuotientRank]
  have e2 : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0 := by
    have s : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) =
        q1 • (i2 * τ0) + τ1 * (m1 * l1 - l1 * m1) * τ0 := by
      rw [← Y1']
      simp only [add_mul, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]
      abel
    rw [s, K, sub_mul, smul_mul_assoc, smul_mul_assoc, h00', Algebra.algebraMap_eq_smul_one]
    abel
  have F1 : τ1 * l1 * i1 = l0 := by rw [← Y1, mul_assoc, h11, mul_one]
  have F2 : τ0 * m0 * i0 = m1 := by rw [← Y1', mul_assoc, h00, mul_one]
  refine ⟨?_, e2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have s : (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) =
        ((q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0)) * l0 - q0 • (τ1 * l1 * i1) := by
      simp only [mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
      abel
    rw [s, e2, F1, ← Algebra.smul_def, sub_self]
  · have s : τ1 * m1 * (τ0 * l0) = τ1 * (τ0 * m0 * l0) := by
      rw [mul_assoc τ1, ← mul_assoc m1, Y1']
    rw [s, mul_add, mul_smul_comm, h11, Algebra.algebraMap_eq_smul_one]
    abel
  · rw [mul_assoc, Y1', sub_self]
  · have s : (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) =
        q0 • (i1 * τ1 * m1) - τ0 * m0 * (τ1 * (m1 * l1 - l1 * m1)) - q1 • (τ0 * m0 * i2) := by
      have s2 : τ0 * m0 * l0 * (τ1 * m1) = τ0 * m0 * (τ1 * (l1 * m1)) := by
        rw [mul_assoc (τ0 * m0), ← mul_assoc l0, Y1, mul_assoc τ1]
      rw [add_mul, s2]
      simp only [mul_add, mul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]
      abel
    rw [s, K, h11', one_mul, mul_sub, mul_smul_comm, mul_smul_comm, F2]
    abel
  · rw [add_mul, smul_mul_assoc, h11', mul_assoc (τ0 * m0) l0 τ1, Y1, Algebra.algebraMap_eq_smul_one]
    abel
  · have s : τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) =
        -(τ0 * (τ1 * (m1 * l1 - l1 * m1))) - q1 • (τ0 * i2) := by
      have s2 : τ0 * l0 * (τ1 * m1) = τ0 * (τ1 * (l1 * m1)) := by
        rw [mul_assoc τ0, ← mul_assoc l0, Y1, mul_assoc]
      rw [s2]
      simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]
      abel
    rw [s, K, mul_sub, mul_smul_comm, mul_smul_comm, h00, Algebra.algebraMap_eq_smul_one]
    abel
  · rw [mul_assoc, Y1, sub_self]

open Matrix in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `(norm := noncomm_ring) e1`. Take the linear combination `(norm := noncomm_ring) e2`. Take the linear combination `(norm := noncomm_ring) e3`.

Take the linear combination `(norm := noncomm_ring) e4`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`. Take the linear combination `(norm := noncomm_ring) e5`. Take the linear combination `(norm := noncomm_ring) e6`. Take the linear combination `(norm := noncomm_ring) e7`.

Take the linear combination `(norm := noncomm_ring) e8`.
-/
theorem isSymplectic_of_eight_relations (a b c d a' b' c' d' q : B)
    (e1 : a' * c - c' * a = 0) (e2 : a' * d - c' * b = q) (e3 : b' * c - d' * a = -q) (e4 : b' * d - d' * b = 0)
    (e5 : a * b' - b * a' = 0) (e6 : a * d' - b * c' = q) (e7 : c * b' - d * a' = -q) (e8 : c * d' - d * c' = 0) :
    (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ * Formalism.YangianSpanCharacter.T.J B * !![a, b; c, d] = q • Formalism.YangianSpanCharacter.T.J B ∧
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) B) * Formalism.YangianSpanCharacter.T.J B * (!![a', b'; c', d'] : Matrix (Fin 2) (Fin 2) B)ᵀ = q • Formalism.YangianSpanCharacter.T.J B := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (norm := noncomm_ring) e1
    · linear_combination (norm := noncomm_ring) e2
    · linear_combination (norm := noncomm_ring) e3
    · linear_combination (norm := noncomm_ring) e4
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (norm := noncomm_ring) e5
    · linear_combination (norm := noncomm_ring) e6
    · linear_combination (norm := noncomm_ring) e7
    · linear_combination (norm := noncomm_ring) e8

end AbsDet

end PartA

section PartB

open  Formalism.FourierDecayAlt Finset
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

section abs2

variable {R : Type*} [Ring R] [Algebra ℂ R]

/- English proof (translation)
Establish `a : L0 * (G * X) = G * X * L1` using `by rw [← mul_assoc, hLG, mul_assoc, mul_assoc, hXL.eq]`. Establish `b : Gi * U * (G * X) = G * X * (Gi * U')`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_mul, mul_add, a, b]`.
-/
theorem lowering_intertwine_gamma (G Gi X L0 L1 U U' : R) (hLG : L0 * G = G * L1) (hXL : Commute X L1) (hUX : U * X = X * U')
    (hGU : Commute G U) (hGiX : Commute Gi X) (hGGi : Commute G Gi) :
    (L0 + Gi * U) * (G * X) = (G * X) * (L1 + Gi * U') := by
  have a : L0 * (G * X) = G * X * L1 := by rw [← mul_assoc, hLG, mul_assoc, mul_assoc, hXL.eq]
  have b : Gi * U * (G * X) = G * X * (Gi * U') := by
    calc Gi * U * (G * X) = Gi * (U * G) * X := by simp only [mul_assoc]
      _ = Gi * (G * U) * X := by rw [hGU.eq]
      _ = (Gi * G) * (U * X) := by simp only [mul_assoc]
      _ = (G * Gi) * (X * U') := by rw [hUX, hGGi.eq]
      _ = G * (Gi * X) * U' := by simp only [mul_assoc]
      _ = G * (X * Gi) * U' := by rw [hGiX.eq]
      _ = _ := by simp only [mul_assoc]
  rw [add_mul, mul_add, a, b]

/- English proof (translation)
Use `show Ns * (Gi * S) = Gi * S * Ns`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nabla_star_commute_gamma_inv (Gi z Ns S : R) (nsGi : Ns * Gi = Gi * Ns + z * Gi * Gi) (hS : Ns * S = S * Ns - z * Gi * S)
    (c : Gi * z = z * Gi) : Commute Ns (Gi * S) := by
  show Ns * (Gi * S) = Gi * S * Ns
  calc Ns * (Gi * S) = (Ns * Gi) * S := (mul_assoc _ _ _).symm
    _ = Gi * (Ns * S) + z * Gi * Gi * S := by rw [nsGi, add_mul, mul_assoc Gi Ns S]
    _ = Gi * S * Ns - (Gi * z) * Gi * S + z * Gi * Gi * S := by rw [hS, mul_sub]; simp only [mul_assoc]
    _ = _ := by rw [c]; abel

/- English proof (translation)
Establish `hzz : z * zb = G + t • 1` using `by rw [hGdef, Algebra.algebraMap_eq_smul_one]; abel`. Establish `w1 : z * zb * Gi * Gi = Gi + t • (Gi * Gi)`. Rewrite using `[hzz, add_mul, add_mul, hGGi, one_mul, smul_mul_assoc, one_mul, smul_mul_assoc]`. Establish `k1 : Ns * (zb * Gi) = (zb * Gi) * Ns + t • (Gi * Gi)`. Combine the equalities or inequalities in the displayed calculation.

Establish `k2 : N * (z * Gi) = (z * Gi) * N - t • (Gi * Gi)`. Combine the equalities or inequalities in the displayed calculation. Establish `k3 : (z * Gi) * (zb * Gi) = (zb * Gi) * (z * Gi)`. Combine the equalities or inequalities in the displayed calculation. Establish `ex : (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) = (Ns * N - N * Ns) + cv • (Ns * (zb * Gi) - (zb * Gi) * Ns) - cu • (N * (z * Gi) - (z * Gi) * N) + (cu * cv) • ((z * Gi) * (zb * Gi) - (zb * Gi) * (z * Gi))`.

Simplify using `only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]`. Use `module`. Rewrite using `[ex, hcurv, k1, k2, k3]`. Use `module`.
-/
theorem absC (G Gi z zb N Ns K : R) (t : ℂ) (hGGi : G * Gi = 1) (hGdef : G = z * zb - algebraMap ℂ R t)
    (czzb : z * zb = zb * z) (cGiz : Gi * z = z * Gi) (cGizb : Gi * zb = zb * Gi)
    (nz : N * z = z * N + 1) (nGi : N * Gi = Gi * N - zb * Gi * Gi)
    (nszb : Ns * zb = zb * Ns - 1) (nsGi : Ns * Gi = Gi * Ns + z * Gi * Gi)
    (hcurv : Ns * N - N * Ns = K * Gi * Gi) (cu cv : ℂ) :
    (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      K * Gi * Gi + ((cu + cv) * t) • (Gi * Gi) := by
  have hzz : z * zb = G + t • 1 := by rw [hGdef, Algebra.algebraMap_eq_smul_one]; abel
  have w1 : z * zb * Gi * Gi = Gi + t • (Gi * Gi) := by
    rw [hzz, add_mul, add_mul, hGGi, one_mul, smul_mul_assoc, one_mul, smul_mul_assoc]
  have k1 : Ns * (zb * Gi) = (zb * Gi) * Ns + t • (Gi * Gi) := by
    calc Ns * (zb * Gi) = (Ns * zb) * Gi := (mul_assoc _ _ _).symm
      _ = zb * (Ns * Gi) - Gi := by rw [nszb, sub_mul, one_mul, mul_assoc]
      _ = zb * Gi * Ns + (zb * z) * Gi * Gi - Gi := by rw [nsGi, mul_add]; simp only [mul_assoc]
      _ = _ := by rw [← czzb, w1]; abel
  have k2 : N * (z * Gi) = (z * Gi) * N - t • (Gi * Gi) := by
    calc N * (z * Gi) = (N * z) * Gi := (mul_assoc _ _ _).symm
      _ = z * (N * Gi) + Gi := by rw [nz, add_mul, one_mul, mul_assoc]
      _ = z * Gi * N - (z * zb) * Gi * Gi + Gi := by rw [nGi, mul_sub]; simp only [mul_assoc]
      _ = _ := by rw [w1]; abel
  have k3 : (z * Gi) * (zb * Gi) = (zb * Gi) * (z * Gi) := by
    calc (z * Gi) * (zb * Gi) = z * (Gi * zb) * Gi := by simp only [mul_assoc]
      _ = (z * zb) * Gi * Gi := by rw [cGizb]; simp only [mul_assoc]
      _ = zb * (z * Gi) * Gi := by rw [czzb]; simp only [mul_assoc]
      _ = zb * (Gi * z) * Gi := by rw [cGiz]
      _ = _ := by simp only [mul_assoc]
  have ex : (-Ns - cu • (z * Gi)) * (-N - cv • (zb * Gi)) - (-N - cv • (zb * Gi)) * (-Ns - cu • (z * Gi)) =
      (Ns * N - N * Ns) + cv • (Ns * (zb * Gi) - (zb * Gi) * Ns) - cu • (N * (z * Gi) - (z * Gi) * N) +
        (cu * cv) • ((z * Gi) * (zb * Gi) - (zb * Gi) * (z * Gi)) := by
    simp only [sub_mul, mul_sub, neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm]
    module
  rw [ex, hcurv, k1, k2, k3]
  module

/- English proof (translation)
Establish `a : Gi * Sm * (Gi * Sl) = Gi * Gi * (Sm * Sl)`. Combine the equalities or inequalities in the displayed calculation. Establish `b : Gi * Sl * (Gi * Sm) = Gi * Gi * (Sl * Sm)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [add_mul, mul_add]`.

Rewrite using `[a, b, hA.eq, hB.eq, mul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem commutator_perturbed_product (M0 L0 Gi Sl Sm : R) (hA : Commute M0 (Gi * Sl)) (hB : Commute L0 (Gi * Sm))
    (hGm : Commute Gi Sm) (hGl : Commute Gi Sl) :
    (M0 + Gi * Sm) * (L0 + Gi * Sl) - (L0 + Gi * Sl) * (M0 + Gi * Sm) =
      (M0 * L0 - L0 * M0) + Gi * Gi * (Sm * Sl - Sl * Sm) := by
  have a : Gi * Sm * (Gi * Sl) = Gi * Gi * (Sm * Sl) := by
    calc Gi * Sm * (Gi * Sl) = Gi * (Sm * Gi) * Sl := by simp only [mul_assoc]
      _ = Gi * (Gi * Sm) * Sl := by rw [hGm.eq]
      _ = _ := by simp only [mul_assoc]
  have b : Gi * Sl * (Gi * Sm) = Gi * Gi * (Sl * Sm) := by
    calc Gi * Sl * (Gi * Sm) = Gi * (Sl * Gi) * Sm := by simp only [mul_assoc]
      _ = Gi * (Gi * Sl) * Sm := by rw [hGl.eq]
      _ = _ := by simp only [mul_assoc]
  simp only [add_mul, mul_add]
  rw [a, b, hA.eq, hB.eq, mul_sub]
  abel

/- English proof (translation)
Establish `e1 : a * Ss * (b * S) = a * b * (Ss * S)`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : b * S * (a * Ss) = b * a * (S * Ss)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2, hab, hm, sub_self]`.
-/
theorem commutator_four_commuting (a b S Ss : R) (h1 : Ss * b = b * Ss) (h2 : S * a = a * S) (hab : a * b = b * a)
    (hm : Ss * S = S * Ss) : a * Ss * (b * S) - b * S * (a * Ss) = 0 := by
  have e1 : a * Ss * (b * S) = a * b * (Ss * S) := by
    calc a * Ss * (b * S) = a * (Ss * b) * S := by simp only [mul_assoc]
      _ = _ := by rw [h1]; simp only [mul_assoc]
  have e2 : b * S * (a * Ss) = b * a * (S * Ss) := by
    calc b * S * (a * Ss) = b * (S * a) * Ss := by simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [mul_assoc]
  rw [e1, e2, hab, hm, sub_self]

/- English proof (translation)
Establish `e1 : a * Ss * (a * S) = a * ap * (Ss * S)`. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : a * S * (a * Ss) = a * am * (S * Ss)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e1, e2, hn, hd]`.
-/
theorem commutator_expansion_identity (a ap am S Ss Nn Nd : R) (h1 : Ss * a = ap * Ss) (h2 : S * a = am * S) (hn : Ss * S = Nn)
    (hd : S * Ss = Nd) : a * Ss * (a * S) - a * S * (a * Ss) = a * ap * Nn - a * am * Nd := by
  have e1 : a * Ss * (a * S) = a * ap * (Ss * S) := by
    calc a * Ss * (a * S) = a * (Ss * a) * S := by simp only [mul_assoc]
      _ = _ := by rw [h1]; simp only [mul_assoc]
  have e2 : a * S * (a * Ss) = a * am * (S * Ss) := by
    calc a * S * (a * Ss) = a * (S * a) * Ss := by simp only [mul_assoc]
      _ = _ := by rw [h2]; simp only [mul_assoc]
  rw [e1, e2, hn, hd]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem absUX (a g S X a' e : R) (s1 : g * S = S * X) (s2 : a * g = e) (s3 : X * a' = e) :
    a * S * X = X * (a' * S) := by
  calc a * S * X = a * (S * X) := mul_assoc _ _ _
    _ = a * (g * S) := by rw [s1]
    _ = (a * g) * S := (mul_assoc _ _ _).symm
    _ = (X * a') * S := by rw [s2, s3]
    _ = _ := mul_assoc _ _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem absInv (G Gi X Xi : R) (hG : G * Gi = 1) (hG' : Gi * G = 1) (hX : X * Xi = 1) (hX' : Xi * X = 1)
    (c : Commute X Gi) (c' : Commute Xi G) : (G * X) * (Gi * Xi) = 1 ∧ (Gi * Xi) * (G * X) = 1 := by
  constructor
  · calc (G * X) * (Gi * Xi) = G * (X * Gi) * Xi := by simp only [mul_assoc]
      _ = (G * Gi) * (X * Xi) := by rw [c.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hG, hX, one_mul]
  · calc (Gi * Xi) * (G * X) = Gi * (Xi * G) * X := by simp only [mul_assoc]
      _ = (Gi * G) * (Xi * X) := by rw [c'.eq]; simp only [mul_assoc]
      _ = 1 := by rw [hG', hX', one_mul]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem absTi (Gi a b : R) (c : Commute a Gi) : (Gi * a) * (Gi * b) = Gi * Gi * (a * b) := by
  calc (Gi * a) * (Gi * b) = Gi * (a * Gi) * b := by simp only [mul_assoc]
    _ = _ := by rw [c.eq]; simp only [mul_assoc]

/- English proof (translation)
Establish `: Gi * (k * S) = k * (Gi * S)` using `by rw [← mul_assoc, c.eq, mul_assoc]`. Rewrite using `[this]`. Conclude with `h1.mul_right h2`.
-/
theorem absTerm (X k Gi S : R) (h1 : Commute X k) (h2 : Commute X (Gi * S)) (c : Commute Gi k) :
    Commute X (Gi * (k * S)) := by
  have : Gi * (k * S) = k * (Gi * S) := by rw [← mul_assoc, c.eq, mul_assoc]
  rw [this]; exact h1.mul_right h2

/- English proof (translation)
Rewrite using `[absLG G b zb N hNG hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]`.
-/
theorem absLG2 (G b zb N : R) (hNG : N * G = G * N + zb) (hbG : b * G = G * b) (hGb : G * b = zb) (c c' : ℂ)
    (hc : c' = c + 1) : (-N - c • b) * G = G * (-N - c' • b) := by
  rw [absLG G b zb N hNG hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]

/- English proof (translation)
Establish `hNG' : N * G = G * N + -z` using `by rw [hNG, sub_eq_add_neg]`. Rewrite using `[absLG G b (-z) N hNG' hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]`. Normalize the expressions using the abelian group laws.
-/
theorem absLG3 (G b z N : R) (hNG : N * G = G * N - z) (hbG : b * G = G * b) (hGb : G * b = z) (c c' : ℂ)
    (hc : c = c' + 1) : (-N - c • b) * G = G * (-N - c' • b) := by
  have hNG' : N * G = G * N + -z := by rw [hNG, sub_eq_add_neg]
  rw [absLG G b (-z) N hNG' hbG, hc, add_smul, one_smul, ← sub_sub, mul_sub G _ b, hGb]
  abel

/- English proof (translation)
Establish `: K * Gi * Gi = Gi * Gi * K` using `by rw [h.eq, mul_assoc, h.eq, mul_assoc]`. Rewrite using `[this, mul_add, mul_add, mul_smul_comm, mul_one]`.
-/
theorem absFin (Gi K S : R) (c : ℂ) (h : Commute K Gi) :
    K * Gi * Gi + c • (Gi * Gi) + Gi * Gi * S = Gi * Gi * (K + c • 1 + S) := by
  have : K * Gi * Gi = Gi * Gi * K := by rw [h.eq, mul_assoc, h.eq, mul_assoc]
  rw [this, mul_add, mul_add, mul_smul_comm, mul_one]

end abs2

/- English proof (translation)
Rewrite using `[← map_mul]`. Conclude with `congrArg (kap P D) (funext e)`.
-/
theorem kap_mul (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f g h : Ty P → ℂ) (e : ∀ π, f π * g π = h π) : kap P D f * kap P D g = kap P D h := by
  rw [← map_mul]; exact congrArg (kap P D) (funext e)

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congrArg Matrix.diagonal (funext fun π => ?_)` and prove the remaining obligations. Conclude with `(algebraMap_star_comm (f π)).symm`.
-/
theorem star_kap (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) : star (kap P D f) = kap P D (fun π => star (f π)) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun π => ?_)
  exact (algebraMap_star_comm (f π)).symm

/- English proof (translation)
Use `show sc P D _ * sc P D _ = sc P D _ * sc P D _`. Establish `h : ∀ a b : D.Pr, sc P D a * sc P D b = sc P D (a * b)` using `fun a b => (map_mul (Matrix.scalar (Ty P)) a b).symm`. Rewrite using `[h, h, multiplierPair_comm D]`.
-/
theorem fn_comm (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f fb g gb : D.R) : Commute (sc P D (D.fnP f fb)) (sc P D (D.fnP g gb)) := by
  show sc P D _ * sc P D _ = sc P D _ * sc P D _
  have h : ∀ a b : D.Pr, sc P D a * sc P D b = sc P D (a * b) := fun a b => (map_mul (Matrix.scalar (Ty P)) a b).symm
  rw [h, h, multiplierPair_comm D]

/- English proof (translation)
Establish `h` using `(hSc P D l (star w)).star_star`. Rewrite `h` using `[star_sc, star_star]`. Conclude with `h.symm`.
-/
theorem sc_SSs (hSc : SSScalar) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (w : D.Pr) : Commute (sc P D w) (star (SS P D l)) := by
  have h := (hSc P D l (star w)).star_star
  rw [star_sc, star_star] at h
  exact h.symm

/- English proof (translation)
Establish `h1` using `hSh P D l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by simp only [h π π' hu])`. Establish `h2` using `congrArg star h1`. Rewrite `h2` using `[star_mul, star_mul, star_kap, star_kap]`. Simplify `h2` using `only [star_star]`.
-/
theorem shS (hSh : SSShift) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (f g : Ty P → ℂ) (h : ∀ π π', Up P l π π' → g π' = f π) :
    star (SS P D l) * kap P D g = kap P D f * star (SS P D l) := by
  have h1 := hSh P D l (fun π => star (f π)) (fun π => star (g π)) (fun π π' hu => by simp only [h π π' hu])
  have h2 := congrArg star h1
  rw [star_mul, star_mul, star_kap, star_kap] at h2
  simpa only [star_star] using h2

/- English proof (translation)
Rewrite `h` using `[xC_eq P π Y j hj]`. Conclude with `right_ne_zero_of_mul h`.
-/
theorem fac_ne (P : Par) (π : Ty P) (Y : ℂ) (j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (h : xC P π Y ≠ 0) :
    Y + (rho P π j : ℂ) ≠ 0 := by
  rw [xC_eq P π Y j hj] at h; exact right_ne_zero_of_mul h

noncomputable def ti (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : A P D := ggiA P D * kap P D fun π => (xC P π Y)⁻¹

noncomputable def Ul (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : A P D :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j

noncomputable def Um (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : A P D :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P D j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lA_eq (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : lA P D Y = l0A P D Y + ggiA P D * Ul P D Y := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mA_eq (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : mA P D Y = m0A P D Y + ggiA P D * Um P D Y := rfl

/- English proof (translation)
Rewrite using `[m0A, Algebra.smul_def]`.
-/
theorem raising_constant_eq_shift (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : m0A P D Y = -nabsA P D - (Y - 1 / 2) • (zA P D * ggiA P D) := by
  rw [m0A, Algebra.smul_def]

/- English proof (translation)
Unfold `Ul`. Conclude with `Commute.sum_right _ _ _ (fun j _ => ((kap_comm_sc P D _ w).symm).mul_right (hSc P D j w).symm)`.
-/
theorem sc_Ul (hSc : SSScalar) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (w : D.Pr) (Y : ℂ) : Commute (sc P D w) (Ul P D Y) := by
  unfold Ul
  exact Commute.sum_right _ _ _ (fun j _ => ((kap_comm_sc P D _ w).symm).mul_right (hSc P D j w).symm)

/- English proof (translation)
Unfold `Um`. Conclude with `Commute.sum_right _ _ _ (fun j _ => ((kap_comm_sc P D _ w).symm).mul_right (sc_SSs hSc P D j w))`.
-/
theorem sc_Um (hSc : SSScalar) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (w : D.Pr) (Y : ℂ) : Commute (sc P D w) (Um P D Y) := by
  unfold Um
  exact Commute.sum_right _ _ _ (fun j _ => ((kap_comm_sc P D _ w).symm).mul_right (sc_SSs hSc P D j w))

/- English proof (translation)
Unfold `Ul`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `s1 : (kap P D fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) * SS P D j = SS P D j * xA P D (Y + 1)` using `hSh P D j _ _ (fun π π' hU => by show xEx P {j} π' (Y + 1) * (Y + (rho P π' j : ℂ)) = xC P π (Y + 1)`. Rewrite using `[xC_eq P π (Y + 1) j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]`.

Use `push_cast`. Use the proof step `ring)`. Establish `s2 : (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * (kap P D fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) = kap P D fun π => xEx P {j} π (Y + 1)` using `kap_mul P D _ _ _ (fun π => by show (Y + (rho P π j : ℂ))⁻¹ * (xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) = xEx P {j} π (Y + 1)`. Use `fac_ne P π Y j hj (h0 π)` as an intermediate fact. Use the proof step `field_simp)`.

Establish `s3 : xA P D (Y + 1) * (kap P D fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) = kap P D fun π => xEx P {j} π (Y + 1)` using `kap_mul P D _ _ _ (fun π => by show xC P π (Y + 1) * (Y + 1 + (rho P π j : ℂ))⁻¹ = xEx P {j} π (Y + 1)`. Use `fac_ne P π (Y + 1) j hj (h1 π)` as an intermediate fact. Rewrite using `[xC_eq P π (Y + 1) j hj]`. Use the proof step `field_simp)`. Conclude with `absUX _ _ _ _ _ _ s1 s2 s3`.
-/
theorem lower_shift_commute_coordinate (hSh : SSShift) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0)
    (h1 : ∀ π, xC P π (Y + 1) ≠ 0) : Ul P D Y * xA P D (Y + 1) = xA P D (Y + 1) * Ul P D (Y + 1) := by
  unfold Ul
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have s1 : (kap P D fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) * SS P D j = SS P D j * xA P D (Y + 1) :=
    hSh P D j _ _ (fun π π' hU => by
      show xEx P {j} π' (Y + 1) * (Y + (rho P π' j : ℂ)) = xC P π (Y + 1)
      rw [xC_eq P π (Y + 1) j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]
      push_cast; ring)
  have s2 : (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * (kap P D fun π => xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) =
      kap P D fun π => xEx P {j} π (Y + 1) :=
    kap_mul P D _ _ _ (fun π => by
      show (Y + (rho P π j : ℂ))⁻¹ * (xEx P {j} π (Y + 1) * (Y + (rho P π j : ℂ))) = xEx P {j} π (Y + 1)
      have := fac_ne P π Y j hj (h0 π)
      field_simp)
  have s3 : xA P D (Y + 1) * (kap P D fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) = kap P D fun π => xEx P {j} π (Y + 1) :=
    kap_mul P D _ _ _ (fun π => by
      show xC P π (Y + 1) * (Y + 1 + (rho P π j : ℂ))⁻¹ = xEx P {j} π (Y + 1)
      have := fac_ne P π (Y + 1) j hj (h1 π)
      rw [xC_eq P π (Y + 1) j hj]; field_simp)
  exact absUX _ _ _ _ _ _ s1 s2 s3

/- English proof (translation)
Unfold `Um`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `s1 : (kap P D fun π => xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) * star (SS P D j) = star (SS P D j) * xA P D Y` using `(shS hSh P D j _ _ (fun π π' hU => by show xC P π' Y = xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))`. Rewrite using `[xC_eq P π' Y j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]`.

Use `push_cast`. Use the proof step `ring)).symm`. Establish `s2 : (kap P D fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) * (kap P D fun π => xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) = kap P D fun π => xEx P {j} π Y` using `kap_mul P D _ _ _ (fun π => by show (Y + 1 + (rho P π j : ℂ))⁻¹ * (xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) = xEx P {j} π Y`. Use `fac_ne P π (Y + 1) j hj (h1 π)` as an intermediate fact. Use the proof step `field_simp)`.

Establish `s3 : xA P D Y * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P D fun π => xEx P {j} π Y` using `kap_mul P D _ _ _ (fun π => by show xC P π Y * (Y + (rho P π j : ℂ))⁻¹ = xEx P {j} π Y`. Use `fac_ne P π Y j hj (h0 π)` as an intermediate fact. Rewrite using `[xC_eq P π Y j hj]`. Use the proof step `field_simp)`. Conclude with `absUX _ _ _ _ _ _ s1 s2 s3`.
-/
theorem upper_shift_commute_coordinate (hSh : SSShift) (hR : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0)
    (h1 : ∀ π, xC P π (Y + 1) ≠ 0) : Um P D (Y + 1) * xA P D Y = xA P D Y * Um P D Y := by
  unfold Um
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have s1 : (kap P D fun π => xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) * star (SS P D j) = star (SS P D j) * xA P D Y :=
    (shS hSh P D j _ _ (fun π π' hU => by
      show xC P π' Y = xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))
      rw [xC_eq P π' Y j hj, xEx_up hR P j π π' hU {j} (Finset.mem_singleton_self j), rho_up hR P j hj π π' hU]
      push_cast; ring)).symm
  have s2 : (kap P D fun π => (Y + 1 + (rho P π j : ℂ))⁻¹) * (kap P D fun π => xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) =
      kap P D fun π => xEx P {j} π Y :=
    kap_mul P D _ _ _ (fun π => by
      show (Y + 1 + (rho P π j : ℂ))⁻¹ * (xEx P {j} π Y * (Y + 1 + (rho P π j : ℂ))) = xEx P {j} π Y
      have := fac_ne P π (Y + 1) j hj (h1 π)
      field_simp)
  have s3 : xA P D Y * (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) = kap P D fun π => xEx P {j} π Y :=
    kap_mul P D _ _ _ (fun π => by
      show xC P π Y * (Y + (rho P π j : ℂ))⁻¹ = xEx P {j} π Y
      have := fac_ne P π Y j hj (h0 π)
      rw [xC_eq P π Y j hj]; field_simp)
  exact absUX _ _ _ _ _ _ s1 s2 s3

/- English proof (translation)
Take `⟨_, _, _, _, _, _, hGGi, hGiG, _⟩` from `hLF P D`. Establish `hX : xA P D Y * (kap P D fun π => (xC P π Y)⁻¹) = 1` using `(kap_mul P D _ _ (fun _ => 1) (fun π => mul_inv_cancel₀ (h π))).trans (map_one (kap P D))`. Establish `hX' : (kap P D fun π => (xC P π Y)⁻¹) * xA P D Y = 1` using `(kap_mul P D _ _ (fun _ => 1) (fun π => inv_mul_cancel₀ (h π))).trans (map_one (kap P D))`. Conclude with `absInv _ _ _ _ hGGi hGiG hX hX' (kap_comm_sc P D _ _) (kap_comm_sc P D _ _)`.
-/
theorem monodromy_diagonal_inverse (hLF : LevFns) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) (h : ∀ π, xC P π Y ≠ 0) :
    t22 P D Y * ti P D Y = 1 ∧ ti P D Y * t22 P D Y = 1 := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P D
  have hX : xA P D Y * (kap P D fun π => (xC P π Y)⁻¹) = 1 :=
    (kap_mul P D _ _ (fun _ => 1) (fun π => mul_inv_cancel₀ (h π))).trans (map_one (kap P D))
  have hX' : (kap P D fun π => (xC P π Y)⁻¹) * xA P D Y = 1 :=
    (kap_mul P D _ _ (fun _ => 1) (fun π => inv_mul_cancel₀ (h π))).trans (map_one (kap P D))
  exact absInv _ _ _ _ hGGi hGiG hX hX' (kap_comm_sc P D _ _) (kap_comm_sc P D _ _)

/- English proof (translation)
Unfold `ti`. Establish `c : Commute (kap P D fun π => (xC P π a)⁻¹) (ggiA P D)` using `kap_comm_sc P D _ _`. Rewrite using `[absTi _ _ _ c, kap_mul P D _ _ _ (fun π => rfl)]`.
-/
theorem ti_mul (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (a b : ℂ) :
    ti P D a * ti P D b = ggiA P D * ggiA P D * kap P D fun π => (xC P π a)⁻¹ * (xC P π b)⁻¹ := by
  unfold ti
  have c : Commute (kap P D fun π => (xC P π a)⁻¹) (ggiA P D) := kap_comm_sc P D _ _
  rw [absTi _ _ _ c, kap_mul P D _ _ _ (fun π => rfl)]

/- English proof (translation)
Rewrite using `[ti_mul, ti_mul]`. Conclude with `congrArg (fun t => ggiA P D * ggiA P D * kap P D t) (funext fun π => mul_comm _ _)`.
-/
theorem ti_comm (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (a b : ℂ) : ti P D a * ti P D b = ti P D b * ti P D a := by
  rw [ti_mul, ti_mul]
  exact congrArg (fun t => ggiA P D * ggiA P D * kap P D t) (funext fun π => mul_comm _ _)

/- English proof (translation)
Rewrite using `[lowering_constant_eq_shift]`. Conclude with `((kap_comm_nab P D f).neg_right).sub_right (((kap_comm_sc P D f _).mul_right (kap_comm_sc P D f _)).smul_right _)`.
-/
theorem kappa_commute_l0 (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P D f) (l0A P D Y) := by
  rw [lowering_constant_eq_shift]
  exact ((kap_comm_nab P D f).neg_right).sub_right
    (((kap_comm_sc P D f _).mul_right (kap_comm_sc P D f _)).smul_right _)

/- English proof (translation)
Rewrite using `[raising_constant_eq_shift]`. Conclude with `((kap_comm_nabs P D f).neg_right).sub_right (((kap_comm_sc P D f _).mul_right (kap_comm_sc P D f _)).smul_right _)`.
-/
theorem kappa_commute_raising_constant (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) (Y : ℂ) : Commute (kap P D f) (m0A P D Y) := by
  rw [raising_constant_eq_shift]
  exact ((kap_comm_nabs P D f).neg_right).sub_right
    (((kap_comm_sc P D f _).mul_right (kap_comm_sc P D f _)).smul_right _)

/- English proof (translation)
Take `⟨_, _, _, _, _, _, hGGi, hGiG, _⟩` from `hLF P D`. Take `⟨_, _, _, _, nG, _, _⟩` from `hLN P D`. Establish `cGzb : Commute (ggA P D) (zbA P D)` using `fn_comm P D _ _ _ _`. Establish `cGGi : Commute (ggA P D) (ggiA P D)` using `fn_comm P D _ _ _ _`. Establish `hGb : ggA P D * (zbA P D * ggiA P D) = zbA P D` using `by rw [← mul_assoc, cGzb.eq, mul_assoc, hGGi, mul_one]`.

Establish `hbG : (zbA P D * ggiA P D) * ggA P D = ggA P D * (zbA P D * ggiA P D)` using `(cGzb.mul_right cGGi).eq.symm`. Establish `hLG : l0A P D Y * ggA P D = ggA P D * l0A P D (Y + 1)`. Rewrite using `[lowering_constant_eq_shift, lowering_constant_eq_shift]`. Conclude with `absLG2 _ _ _ _ nG hbG hGb _ _ (by ring)`. Rewrite using `[lA_eq, lA_eq, t22]`.

Conclude with `lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_l0 P D _ _) (lower_shift_commute_coordinate hSh hR P D Y h0 h1) (sc_Ul hSc P D _ _) (kap_comm_sc P D _ _).symm cGGi`.
-/
theorem l_mul_t22_shift (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    lA P D Y * t22 P D (Y + 1) = t22 P D (Y + 1) * lA P D (Y + 1) := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P D
  obtain ⟨_, _, _, _, nG, _, _⟩ := hLN P D
  have cGzb : Commute (ggA P D) (zbA P D) := fn_comm P D _ _ _ _
  have cGGi : Commute (ggA P D) (ggiA P D) := fn_comm P D _ _ _ _
  have hGb : ggA P D * (zbA P D * ggiA P D) = zbA P D := by rw [← mul_assoc, cGzb.eq, mul_assoc, hGGi, mul_one]
  have hbG : (zbA P D * ggiA P D) * ggA P D = ggA P D * (zbA P D * ggiA P D) := (cGzb.mul_right cGGi).eq.symm
  have hLG : l0A P D Y * ggA P D = ggA P D * l0A P D (Y + 1) := by
    rw [lowering_constant_eq_shift, lowering_constant_eq_shift]
    exact absLG2 _ _ _ _ nG hbG hGb _ _ (by ring)
  rw [lA_eq, lA_eq, t22]
  exact lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_l0 P D _ _) (lower_shift_commute_coordinate hSh hR P D Y h0 h1) (sc_Ul hSc P D _ _)
    (kap_comm_sc P D _ _).symm cGGi

/- English proof (translation)
Take `⟨_, _, _, _, _, _, hGGi, hGiG, _⟩` from `hLF P D`. Take `⟨_, _, _, _, nG, _, _⟩` from `hLNs P D`. Establish `cGz : Commute (ggA P D) (zA P D)` using `fn_comm P D _ _ _ _`. Establish `cGGi : Commute (ggA P D) (ggiA P D)` using `fn_comm P D _ _ _ _`. Establish `hGb : ggA P D * (zA P D * ggiA P D) = zA P D` using `by rw [← mul_assoc, cGz.eq, mul_assoc, hGGi, mul_one]`.

Establish `hbG : (zA P D * ggiA P D) * ggA P D = ggA P D * (zA P D * ggiA P D)` using `(cGz.mul_right cGGi).eq.symm`. Establish `hLG : m0A P D (Y + 1) * ggA P D = ggA P D * m0A P D Y`. Rewrite using `[raising_constant_eq_shift, raising_constant_eq_shift]`. Conclude with `absLG3 _ _ _ _ nG hbG hGb _ _ (by ring)`. Rewrite using `[mA_eq, mA_eq, t22]`.

Conclude with `lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_raising_constant P D _ _) (upper_shift_commute_coordinate hSh hR P D Y h0 h1) (sc_Um hSc P D _ _) (kap_comm_sc P D _ _).symm cGGi`.
-/
theorem modY1' (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLNs : LevNabs) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ)
    (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0) :
    mA P D (Y + 1) * t22 P D Y = t22 P D Y * mA P D Y := by
  obtain ⟨_, _, _, _, _, _, hGGi, hGiG, _⟩ := hLF P D
  obtain ⟨_, _, _, _, nG, _, _⟩ := hLNs P D
  have cGz : Commute (ggA P D) (zA P D) := fn_comm P D _ _ _ _
  have cGGi : Commute (ggA P D) (ggiA P D) := fn_comm P D _ _ _ _
  have hGb : ggA P D * (zA P D * ggiA P D) = zA P D := by rw [← mul_assoc, cGz.eq, mul_assoc, hGGi, mul_one]
  have hbG : (zA P D * ggiA P D) * ggA P D = ggA P D * (zA P D * ggiA P D) := (cGz.mul_right cGGi).eq.symm
  have hLG : m0A P D (Y + 1) * ggA P D = ggA P D * m0A P D Y := by
    rw [raising_constant_eq_shift, raising_constant_eq_shift]
    exact absLG3 _ _ _ _ nG hbG hGb _ _ (by ring)
  rw [mA_eq, mA_eq, t22]
  exact lowering_intertwine_gamma _ _ _ _ _ _ _ hLG (kappa_commute_raising_constant P D _ _) (upper_shift_commute_coordinate hSh hR P D Y h0 h1) (sc_Um hSc P D _ _)
    (kap_comm_sc P D _ _).symm cGGi

end PartB

section PartC

open  Formalism.FourierDecayAlt Finset
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

/- English proof (translation)
Take `⟨_, hz, _, _, hGi, hnab⟩` from `hSG P D`. Establish `h` using `congrArg star (hN P D l hl).2`. Establish `hns : star (nabsA P D) = nabA P D` using `by rw [← hnab, star_star]`. Simplify using `only [star_mul, star_sub] at h`. Rewrite `h` using `[hns, hz, hGi]`.

Establish `cg : Commute (ggiA P D) (star (SS P D l))` using `sc_SSs hSc P D l _`. Establish `cz : Commute (zbA P D) (star (SS P D l))` using `sc_SSs hSc P D l _`. Establish `cc : Commute (ggiA P D) (zbA P D)` using `fn_comm P D _ _ _ _`. Establish `c1 : star (SS P D l) * (ggiA P D * zbA P D) = zbA P D * ggiA P D * star (SS P D l)`. Rewrite using `[(cg.mul_left cz).eq.symm, cc.eq]`.

Rewrite `h` using `[c1]`. Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem nab_SSs (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    nabA P D * star (SS P D l) = star (SS P D l) * nabA P D + zbA P D * ggiA P D * star (SS P D l) := by
  obtain ⟨_, hz, _, _, hGi, hnab⟩ := hSG P D
  have h := congrArg star (hN P D l hl).2
  have hns : star (nabsA P D) = nabA P D := by rw [← hnab, star_star]
  simp only [star_mul, star_sub] at h
  rw [hns, hz, hGi] at h
  have cg : Commute (ggiA P D) (star (SS P D l)) := sc_SSs hSc P D l _
  have cz : Commute (zbA P D) (star (SS P D l)) := sc_SSs hSc P D l _
  have cc : Commute (ggiA P D) (zbA P D) := fn_comm P D _ _ _ _
  have c1 : star (SS P D l) * (ggiA P D * zbA P D) = zbA P D * ggiA P D * star (SS P D l) := by
    rw [(cg.mul_left cz).eq.symm, cc.eq]
  rw [c1] at h
  rw [h]; abel

/- English proof (translation)
Take `⟨_, _, _, _, _, nsGi, _⟩` from `hLNs P D`. Establish `cGiz : Commute (ggiA P D) (zA P D)` using `fn_comm P D _ _ _ _`. Establish `h1 : Commute (nabsA P D) (ggiA P D * Ul P D u)`. Unfold `Ul`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nabs P D _).symm (nabla_star_commute_gamma_inv _ _ _ _ nsGi (hN P D j hj).2 cGiz.eq) (kap_comm_sc P D _ _).symm)`. Establish `h2 : Commute (zA P D * ggiA P D) (ggiA P D * Ul P D u)` using `(cGiz.symm.mul_right (sc_Ul hSc P D _ _)).mul_left ((Commute.refl _).mul_right (sc_Ul hSc P D _ _))`. Rewrite using `[raising_constant_eq_shift]`. Conclude with `(h1.neg_left).sub_left (h2.smul_left _)`.
-/
theorem commute_m0_Ul (hSc : SSScalar) (hN : NabSS) (hLNs : LevNabs) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (u : ℂ) :
    Commute (m0A P D u) (ggiA P D * Ul P D u) := by
  obtain ⟨_, _, _, _, _, nsGi, _⟩ := hLNs P D
  have cGiz : Commute (ggiA P D) (zA P D) := fn_comm P D _ _ _ _
  have h1 : Commute (nabsA P D) (ggiA P D * Ul P D u) := by
    unfold Ul; rw [Finset.mul_sum]
    exact Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nabs P D _).symm
      (nabla_star_commute_gamma_inv _ _ _ _ nsGi (hN P D j hj).2 cGiz.eq) (kap_comm_sc P D _ _).symm)
  have h2 : Commute (zA P D * ggiA P D) (ggiA P D * Ul P D u) :=
    (cGiz.symm.mul_right (sc_Ul hSc P D _ _)).mul_left ((Commute.refl _).mul_right (sc_Ul hSc P D _ _))
  rw [raising_constant_eq_shift]; exact (h1.neg_left).sub_left (h2.smul_left _)

/- English proof (translation)
Take `⟨_, _, _, _, _, nGi, _⟩` from `hLN P D`. Establish `cGiz : Commute (ggiA P D) (zbA P D)` using `fn_comm P D _ _ _ _`. Establish `nGi' : nabA P D * ggiA P D = ggiA P D * nabA P D + -zbA P D * ggiA P D * ggiA P D`. Rewrite using `[nGi, neg_mul, neg_mul, sub_eq_add_neg]`. Establish `h1 : Commute (nabA P D) (ggiA P D * Um P D u)`.

Unfold `Um`. Rewrite using `[Finset.mul_sum]`. Conclude with `Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nab P D _).symm (nabla_star_commute_gamma_inv _ _ _ _ nGi' (by rw [nab_SSs hSc hN hSG P D j hj, neg_mul, neg_mul, sub_neg_eq_add]) (by rw [mul_neg, neg_mul, cGiz.eq])) (kap_comm_sc P D _ _).symm)`. Establish `h2 : Commute (zbA P D * ggiA P D) (ggiA P D * Um P D u)` using `(cGiz.symm.mul_right (sc_Um hSc P D _ _)).mul_left ((Commute.refl _).mul_right (sc_Um hSc P D _ _))`. Rewrite using `[lowering_constant_eq_shift]`.

Conclude with `(h1.neg_left).sub_left (h2.smul_left _)`.
-/
theorem commute_l0_Um (hSc : SSScalar) (hN : NabSS) (hSG : StarGens) (hLN : LevNab) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (u : ℂ) :
    Commute (l0A P D u) (ggiA P D * Um P D u) := by
  obtain ⟨_, _, _, _, _, nGi, _⟩ := hLN P D
  have cGiz : Commute (ggiA P D) (zbA P D) := fn_comm P D _ _ _ _
  have nGi' : nabA P D * ggiA P D = ggiA P D * nabA P D + -zbA P D * ggiA P D * ggiA P D := by
    rw [nGi, neg_mul, neg_mul, sub_eq_add_neg]
  have h1 : Commute (nabA P D) (ggiA P D * Um P D u) := by
    unfold Um; rw [Finset.mul_sum]
    exact Commute.sum_right _ _ _ (fun j hj => absTerm _ _ _ _ (kap_comm_nab P D _).symm
      (nabla_star_commute_gamma_inv _ _ _ _ nGi' (by rw [nab_SSs hSc hN hSG P D j hj, neg_mul, neg_mul, sub_neg_eq_add])
        (by rw [mul_neg, neg_mul, cGiz.eq])) (kap_comm_sc P D _ _).symm)
  have h2 : Commute (zbA P D * ggiA P D) (ggiA P D * Um P D u) :=
    (cGiz.symm.mul_right (sc_Um hSc P D _ _)).mul_left ((Commute.refl _).mul_right (sc_Um hSc P D _ _))
  rw [lowering_constant_eq_shift]; exact (h1.neg_left).sub_left (h2.smul_left _)

noncomputable def bb (P : Par) (u : ℂ) (j : ℕ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ))⁻¹

/- English proof (translation)
Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single l]`. Establish `h1 : star (SS P D l) * kap P D (bb P u l) = (kap P D fun π => (u + rho P π l + 1)⁻¹) * star (SS P D l)` using `shS hSh P D l _ _ (fun π π' hU => by show (u + (rho P π' l : ℂ))⁻¹ = (u + rho P π l + 1)⁻¹`. Rewrite using `[rho_up hR P l hl π π' hU]`. Use `push_cast`. Rewrite using `[add_assoc])`.

Establish `h2 : SS P D l * kap P D (bb P u l) = (kap P D fun π => (u + rho P π l - 1)⁻¹) * SS P D l` using `(hSh P D l _ _ (fun π π' hU => by show (u + (rho P π' l : ℂ) - 1)⁻¹ = (u + (rho P π l : ℂ))⁻¹`. Rewrite using `[rho_up hR P l hl π π' hU]`. Use `push_cast`. Use `congr 1`. Use the proof step `ring)).symm`.

Rewrite using `[commutator_expansion_identity _ _ _ _ _ _ _ h1 h2 (hNorm P D hP l hl).1 (hNorm P D hP l hl).2, ← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_sub]`. Use `congrArg (kap P D) (funext fun π => ?_)` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, Pi.mul_apply, bb]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j hj hjl`.

Establish `h1 : star (SS P D l) * kap P D (bb P u j) = kap P D (bb P u j) * star (SS P D l)` using `shS hSh P D l _ _ (fun π π' hU => by show (u + (rho P π' j : ℂ))⁻¹ = (u + (rho P π j : ℂ))⁻¹`. Rewrite using `[hR P l π π' hU j hj, if_neg hjl, add_zero])`. Establish `h2 : SS P D j * kap P D (bb P u l) = kap P D (bb P u l) * SS P D j` using `(hSh P D j _ _ (fun π π' hU => by show (u + (rho P π' l : ℂ))⁻¹ = (u + (rho P π l : ℂ))⁻¹`. Rewrite using `[hR P j π π' hU l hl, if_neg (Ne.symm hjl), add_zero])).symm`. Conclude with `commutator_four_commuting _ _ _ _ h1 h2 (kap_comm_kap P D _ _).eq (hMix P D hP l hl j hj hjl)`.

Introduce `h`. Conclude with `absurd hl h`.
-/
theorem per_l (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (u : ℂ)
    (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ j ∈ Icc 1 (P.k - 1), kap P D (bb P u l) * star (SS P D l) * (kap P D (bb P u j) * SS P D j) -
      ∑ j ∈ Icc 1 (P.k - 1), kap P D (bb P u j) * SS P D j * (kap P D (bb P u l) * star (SS P D l)) =
    kap P D fun π => (Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
      (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹) := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single l]
  · have h1 : star (SS P D l) * kap P D (bb P u l) = (kap P D fun π => (u + rho P π l + 1)⁻¹) * star (SS P D l) :=
      shS hSh P D l _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ))⁻¹ = (u + rho P π l + 1)⁻¹
        rw [rho_up hR P l hl π π' hU]; push_cast; rw [add_assoc])
    have h2 : SS P D l * kap P D (bb P u l) = (kap P D fun π => (u + rho P π l - 1)⁻¹) * SS P D l :=
      (hSh P D l _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ) - 1)⁻¹ = (u + (rho P π l : ℂ))⁻¹
        rw [rho_up hR P l hl π π' hU]; push_cast; congr 1; ring)).symm
    rw [commutator_expansion_identity _ _ _ _ _ _ _ h1 h2 (hNorm P D hP l hl).1 (hNorm P D hP l hl).2, ← map_mul, ← map_mul, ← map_mul,
      ← map_mul, ← map_sub]
    refine congrArg (kap P D) (funext fun π => ?_)
    simp only [Pi.sub_apply, Pi.mul_apply, bb]
    ring
  · intro j hj hjl
    have h1 : star (SS P D l) * kap P D (bb P u j) = kap P D (bb P u j) * star (SS P D l) :=
      shS hSh P D l _ _ (fun π π' hU => by
        show (u + (rho P π' j : ℂ))⁻¹ = (u + (rho P π j : ℂ))⁻¹
        rw [hR P l π π' hU j hj, if_neg hjl, add_zero])
    have h2 : SS P D j * kap P D (bb P u l) = kap P D (bb P u l) * SS P D j :=
      (hSh P D j _ _ (fun π π' hU => by
        show (u + (rho P π' l : ℂ))⁻¹ = (u + (rho P π l : ℂ))⁻¹
        rw [hR P j π π' hU l hl, if_neg (Ne.symm hjl), add_zero])).symm
    exact commutator_four_commuting _ _ _ _ h1 h2 (kap_comm_kap P D _ _).eq (hMix P D hP l hl j hj hjl)
  · intro h; exact absurd hl h

/- English proof (translation)
Establish `e1 : Um P D u * Ul P D u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), kap P D (bb P u l) * star (SS P D l) * (kap P D (bb P u j) * SS P D j)` using `Finset.sum_mul_sum _ _ _ _`. Establish `e2 : Ul P D u * Um P D u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1), kap P D (bb P u j) * SS P D j * (kap P D (bb P u l) * star (SS P D l))` using `(Finset.sum_mul_sum _ _ _ _).trans Finset.sum_comm`. Rewrite using `[e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (per_l hSh hR hNorm hMix P D hP u), ← map_sum]`. Conclude with `congrArg (kap P D) (funext fun π => Finset.sum_apply _ _ _)`.
-/
theorem UmUl (hSh : SSShift) (hR : RhoUp) (hNorm : SSNorm) (hMix : SSMixed) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (u : ℂ) :
    Um P D u * Ul P D u - Ul P D u * Um P D u =
      kap P D fun π => ∑ l ∈ Icc 1 (P.k - 1), ((Nrm P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l + 1)⁻¹) -
        (NrmDown P l π : ℂ) * ((u + rho P π l)⁻¹ * (u + rho P π l - 1)⁻¹)) := by
  have e1 : Um P D u * Ul P D u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      kap P D (bb P u l) * star (SS P D l) * (kap P D (bb P u j) * SS P D j) := Finset.sum_mul_sum _ _ _ _
  have e2 : Ul P D u * Um P D u = ∑ l ∈ Icc 1 (P.k - 1), ∑ j ∈ Icc 1 (P.k - 1),
      kap P D (bb P u j) * SS P D j * (kap P D (bb P u l) * star (SS P D l)) :=
    (Finset.sum_mul_sum _ _ _ _).trans Finset.sum_comm
  rw [e1, e2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl (per_l hSh hR hNorm hMix P D hP u), ← map_sum]
  exact congrArg (kap P D) (funext fun π => Finset.sum_apply _ _ _)

/- English proof (translation)
Take `⟨_, _, _, _, _, _, hGGi, _, hGdef⟩` from `hLF P D`. Take `⟨nz, _, _, _, _, nGi, _⟩` from `hLN P D`. Take `⟨nszb, _, _, _, _, nsGi, _⟩` from `hLNs P D`. Establish `czzb : Commute (zA P D) (zbA P D)` using `fn_comm P D _ _ _ _`. Establish `cGiz : Commute (ggiA P D) (zA P D)` using `fn_comm P D _ _ _ _`.

Establish `cGizb : Commute (ggiA P D) (zbA P D)` using `fn_comm P D _ _ _ _`. Establish `cK : Commute (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) (ggiA P D)` using `kap_comm_sc P D _ _`. Establish `cm : Commute (ggiA P D) (Um P D u)` using `sc_Um hSc P D _ _`. Establish `cl : Commute (ggiA P D) (Ul P D u)` using `sc_Ul hSc P D _ _`. Rewrite using `[mA_eq, lA_eq, commutator_perturbed_product _ _ _ _ _ (commute_m0_Ul hSc hN hLNs P D u) (commute_l0_Um hSc hN hSG hLN P D u) cm cl, UmUl hSh hR hNorm hMix P D hP u, raising_constant_eq_shift, lowering_constant_eq_shift, absC _ _ _ _ _ _ _ _ hGGi hGdef czzb.eq cGiz.eq cGizb.eq nz …`.

Use `congrArg (fun t => ggiA P D * ggiA P D * t) ?_` and prove the remaining obligations. Rewrite using `[← map_smul, ← map_smul, ← map_sub, ← map_one (kap P D), ← map_smul, ← map_add, ← map_add]`. Use `congrArg (kap P D) (funext fun π => ?_)` and prove the remaining obligations. Use `pf P hP π u (h0 π) (h1 π) (h2 π)` as an intermediate fact. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]`.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem raising_lowering_commutator_alt (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature)
    (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (u : ℂ) (h0 : ∀ π, xC P π (u - 1) ≠ 0) (h1 : ∀ π, xC P π u ≠ 0)
    (h2 : ∀ π, xC P π (u + 1) ≠ 0) :
    mA P D u * lA P D u - lA P D u * mA P D u =
      qC P (u - 1) • (ti P D (u - 1) * ti P D u) - qC P u • (ti P D u * ti P D (u + 1)) := by
  obtain ⟨_, _, _, _, _, _, hGGi, _, hGdef⟩ := hLF P D
  obtain ⟨nz, _, _, _, _, nGi, _⟩ := hLN P D
  obtain ⟨nszb, _, _, _, _, nsGi, _⟩ := hLNs P D
  have czzb : Commute (zA P D) (zbA P D) := fn_comm P D _ _ _ _
  have cGiz : Commute (ggiA P D) (zA P D) := fn_comm P D _ _ _ _
  have cGizb : Commute (ggiA P D) (zbA P D) := fn_comm P D _ _ _ _
  have cK : Commute (kap P D fun π => ((2 * aC P π * P.TT : ℝ) : ℂ)) (ggiA P D) := kap_comm_sc P D _ _
  have cm : Commute (ggiA P D) (Um P D u) := sc_Um hSc P D _ _
  have cl : Commute (ggiA P D) (Ul P D u) := sc_Ul hSc P D _ _
  rw [mA_eq, lA_eq, commutator_perturbed_product _ _ _ _ _ (commute_m0_Ul hSc hN hLNs P D u) (commute_l0_Um hSc hN hSG hLN P D u) cm cl,
    UmUl hSh hR hNorm hMix P D hP u, raising_constant_eq_shift, lowering_constant_eq_shift,
    absC _ _ _ _ _ _ _ _ hGGi hGdef czzb.eq cGiz.eq cGizb.eq nz nGi nszb nsGi (hCurv P D), ti_mul, ti_mul,
    absFin _ _ _ _ cK, ← mul_smul_comm, ← mul_smul_comm, ← mul_sub]
  refine congrArg (fun t => ggiA P D * ggiA P D * t) ?_
  rw [← map_smul, ← map_smul, ← map_sub, ← map_one (kap P D), ← map_smul, ← map_add, ← map_add]
  refine congrArg (kap P D) (funext fun π => ?_)
  have := pf P hP π u (h0 π) (h1 π) (h2 π)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul]
  rw [this]; push_cast; ring

def Det8 (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) : Prop :=
  t11 P D (Y + 1) * t21 P D Y - t21 P D (Y + 1) * t11 P D Y = 0 ∧
  t11 P D (Y + 1) * t22 P D Y - t21 P D (Y + 1) * t12 P D Y = algebraMap ℂ (A P D) (qC P Y) ∧
  t12 P D (Y + 1) * t21 P D Y - t22 P D (Y + 1) * t11 P D Y = -algebraMap ℂ (A P D) (qC P Y) ∧
  t12 P D (Y + 1) * t22 P D Y - t22 P D (Y + 1) * t12 P D Y = 0 ∧
  t11 P D Y * t12 P D (Y + 1) - t12 P D Y * t11 P D (Y + 1) = 0 ∧
  t11 P D Y * t22 P D (Y + 1) - t12 P D Y * t21 P D (Y + 1) = algebraMap ℂ (A P D) (qC P Y) ∧
  t21 P D Y * t12 P D (Y + 1) - t22 P D Y * t11 P D (Y + 1) = -algebraMap ℂ (A P D) (qC P Y) ∧
  t21 P D Y * t22 P D (Y + 1) - t22 P D Y * t21 P D (Y + 1) = 0

/- English proof (translation)
Take `⟨a21, a12, a11, _⟩` from `hQN P D hP Y h0`. Take `⟨b21, b12, b11, _⟩` from `hQN P D hP (Y + 1) h1`. Establish `a11' : t11 P D Y = qC P Y • ti P D (Y + 1) + t22 P D Y * mA P D Y * lA P D Y` using `a11 h1`. Establish `b11' : t11 P D (Y + 1) = qC P (Y + 1) • ti P D (Y + 1 + 1) + t22 P D (Y + 1) * mA P D (Y + 1) * lA P D (Y + 1)` using `b11 h2`. Establish `y3` using `raising_lowering_commutator_alt hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv P D hP (Y + 1) (by rw [add_sub_cancel_right]; exact h0) h1 h2`.

Rewrite `y3` using `[add_sub_cancel_right]`. Unfold `Det8`. Rewrite using `[a21, a12, a11', b21, b12, b11']`. Conclude with `det_abs _ _ _ _ _ _ _ _ _ _ _ (monodromy_diagonal_inverse hLF P D Y h0).1 (monodromy_diagonal_inverse hLF P D Y h0).2 (monodromy_diagonal_inverse hLF P D (Y + 1) h1).1 (monodromy_diagonal_inverse hLF P D (Y + 1) h1).2 (ti_comm P D _ _) (l_mul_t22_shift hSc hSh hR hLF hLN P D Y h0 …`.
-/
theorem det_eight_at_good_point (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal)
    (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (Y : ℂ) (h0 : ∀ π, xC P π Y ≠ 0) (h1 : ∀ π, xC P π (Y + 1) ≠ 0)
    (h2 : ∀ π, xC P π (Y + 1 + 1) ≠ 0) : Det8 P D Y := by
  obtain ⟨a21, a12, a11, _⟩ := hQN P D hP Y h0
  obtain ⟨b21, b12, b11, _⟩ := hQN P D hP (Y + 1) h1
  have a11' : t11 P D Y = qC P Y • ti P D (Y + 1) + t22 P D Y * mA P D Y * lA P D Y := a11 h1
  have b11' : t11 P D (Y + 1) = qC P (Y + 1) • ti P D (Y + 1 + 1) + t22 P D (Y + 1) * mA P D (Y + 1) * lA P D (Y + 1) := b11 h2
  have y3 := raising_lowering_commutator_alt hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv P D hP (Y + 1)
    (by rw [add_sub_cancel_right]; exact h0) h1 h2
  rw [add_sub_cancel_right] at y3
  unfold Det8
  rw [a21, a12, a11', b21, b12, b11']
  exact det_abs _ _ _ _ _ _ _ _ _ _ _ (monodromy_diagonal_inverse hLF P D Y h0).1 (monodromy_diagonal_inverse hLF P D Y h0).2 (monodromy_diagonal_inverse hLF P D (Y + 1) h1).1
    (monodromy_diagonal_inverse hLF P D (Y + 1) h1).2 (ti_comm P D _ _) (l_mul_t22_shift hSc hSh hR hLF hLN P D Y h0 h1)
    (modY1' hSc hSh hR hLF hLNs P D Y h0 h1) y3

end PartC

section PartD

open  Formalism.FourierDecayAlt Finset Polynomial
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

/- English proof (translation)
Establish `h : ∀ Y, (kap P D fun π => (p π).eval Y) = ∑ π : Ty P, algebraMap ℂ (A P D) ((p π).eval Y) * kap P D (fun j => if π = j then 1 else 0)`. Introduce `Y`. Use `conv_lhs => rw [pi_eq_sum_univ (fun π => (p π).eval Y)]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Algebra.smul_def]`. Conclude with `(IsPoly.sum _ _ fun π _ => (IsPoly.scalar (p π)).mul (IsPoly.const _)).congr h`.
-/
theorem isPoly_kap (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (p : Ty P → ℂ[X]) : IsPoly (fun Y => kap P D fun π => (p π).eval Y) := by
  have h : ∀ Y, (kap P D fun π => (p π).eval Y) =
      ∑ π : Ty P, algebraMap ℂ (A P D) ((p π).eval Y) * kap P D (fun j => if π = j then 1 else 0) := by
    intro Y
    conv_lhs => rw [pi_eq_sum_univ (fun π => (p π).eval Y)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [map_smul, Algebra.smul_def]
  exact (IsPoly.sum _ _ fun π _ => (IsPoly.scalar (p π)).mul (IsPoly.const _)).congr h

/- English proof (translation)
Simplify using `[xEx, eval_prod]`.
-/
theorem xEx_poly (P : Par) (ex : Finset ℕ) (π : Ty P) (Y : ℂ) :
    xEx P ex π Y = (∏ i ∈ Icc 1 (P.k - 1) \ ex, (X + C (rho P π i : ℂ))).eval Y := by
  simp [xEx, eval_prod]

/- English proof (translation)
Simplify using `[xC, eval_prod]`.
-/
theorem xC_poly (P : Par) (π : Ty P) (Y : ℂ) :
    xC P π Y = (∏ i ∈ Icc 1 (P.k - 1), (X + C (rho P π i : ℂ))).eval Y := by
  simp [xC, eval_prod]

/- English proof (translation)
Simplify using `only [qC, qP, eval_mul, eval_C, eval_prod, eval_add, eval_X]`. Use `congrArg (fun t => -((P.T : ℂ) * P.T') * t) (Finset.prod_congr rfl fun i _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qC_poly (P : Par) (Y : ℂ) : qC P Y = (qP P).eval Y := by
  simp only [qC, qP, eval_mul, eval_C, eval_prod, eval_add, eval_X]
  refine congrArg (fun t => -((P.T : ℂ) * P.T') * t) (Finset.prod_congr rfl fun i _ => ?_)
  ring

/- English proof (translation)
The claim follows from `(isPoly_kap P D _).congr (fun Y => congrArg (kap P D) (funext fun π => xEx_poly P ex π Y))`.
-/
theorem isPoly_xEx (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (ex : Finset ℕ) : IsPoly (fun Y => kap P D fun π => xEx P ex π Y) :=
  (isPoly_kap P D _).congr (fun Y => congrArg (kap P D) (funext fun π => xEx_poly P ex π Y))

/- English proof (translation)
The claim follows from `(isPoly_kap P D _).congr (fun Y => congrArg (kap P D) (funext fun π => xC_poly P π Y))`.
-/
theorem isPoly_xA (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (xA P D) :=
  (isPoly_kap P D _).congr (fun Y => congrArg (kap P D) (funext fun π => xC_poly P π Y))

/- English proof (translation)
The claim follows from `isPoly_kap P D _`.
-/
theorem isPoly_w (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (fun Y => kap P D fun π => wC P π Y) := isPoly_kap P D _

/- English proof (translation)
The claim follows from `(IsPoly.scalar (qP P)).congr (fun Y => by rw [qC_poly])`.
-/
theorem isPoly_q (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (fun Y => algebraMap ℂ (A P D) (qC P Y)) :=
  (IsPoly.scalar (qP P)).congr (fun Y => by rw [qC_poly])

/- English proof (translation)
The claim follows from `((IsPoly.const (-nabA P D)).sub (((IsPoly.scalar (X + C (1 / 2))).mul (IsPoly.const (zbA P D * ggiA P D))))).congr (fun Y => by simp [l0A])`.
-/
theorem isPoly_lowering_constant (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (l0A P D) :=
  ((IsPoly.const (-nabA P D)).sub (((IsPoly.scalar (X + C (1 / 2))).mul (IsPoly.const (zbA P D * ggiA P D))))).congr
    (fun Y => by simp [l0A])

/- English proof (translation)
The claim follows from `((IsPoly.const (-nabsA P D)).sub (((IsPoly.scalar (X - C (1 / 2))).mul (IsPoly.const (zA P D * ggiA P D))))).congr (fun Y => by simp [m0A])`.
-/
theorem isPoly_raising_constant (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (m0A P D) :=
  ((IsPoly.const (-nabsA P D)).sub (((IsPoly.scalar (X - C (1 / 2))).mul (IsPoly.const (zA P D * ggiA P D))))).congr
    (fun Y => by simp [m0A])

/- English proof (translation)
The claim follows from `IsPoly.sum _ _ fun l _ => (IsPoly.const (SS P D l)).mul (isPoly_xEx P D {l})`.
-/
theorem isPoly_S21 (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (weightedSumBis P D) :=
  IsPoly.sum _ _ fun l _ => (IsPoly.const (SS P D l)).mul (isPoly_xEx P D {l})

/- English proof (translation)
The claim follows from `IsPoly.sum _ _ fun l _ => (isPoly_xEx P D {l}).mul (IsPoly.const (star (SS P D l)))`.
-/
theorem isPoly_S12 (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (S12 P D) :=
  IsPoly.sum _ _ fun l _ => (isPoly_xEx P D {l}).mul (IsPoly.const (star (SS P D l)))

/- English proof (translation)
The claim follows from `IsPoly.sum _ _ fun l _ => IsPoly.sum _ _ fun j _ => (IsPoly.const (star (SS P D l) * SS P D j)).mul (isPoly_xEx P D {l, j})`.
-/
theorem isPoly_quartic_sum (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (S4 P D) :=
  IsPoly.sum _ _ fun l _ => IsPoly.sum _ _ fun j _ =>
    (IsPoly.const (star (SS P D l) * SS P D j)).mul (isPoly_xEx P D {l, j})

/- English proof (translation)
The claim follows from `(IsPoly.const (ggA P D)).mul (isPoly_xA P D)`.
-/
theorem isPoly_diagonal_entry (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (t22 P D) := (IsPoly.const (ggA P D)).mul (isPoly_xA P D)

/- English proof (translation)
The claim follows from `(((IsPoly.const (ggA P D)).mul (isPoly_xA P D)).mul (isPoly_lowering_constant P D)).add (isPoly_S21 P D)`.
-/
theorem isPoly_t21 (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (t21 P D) :=
  (((IsPoly.const (ggA P D)).mul (isPoly_xA P D)).mul (isPoly_lowering_constant P D)).add (isPoly_S21 P D)

/- English proof (translation)
The claim follows from `(((IsPoly.const (ggA P D)).mul (isPoly_xA P D)).mul (isPoly_raising_constant P D)).add (isPoly_S12 P D)`.
-/
theorem isPoly_upper_right_entry (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (t12 P D) :=
  (((IsPoly.const (ggA P D)).mul (isPoly_xA P D)).mul (isPoly_raising_constant P D)).add (isPoly_S12 P D)

/- English proof (translation)
The claim follows from `(((((IsPoly.const (ggiA P D)).mul (isPoly_w P D)).add ((((IsPoly.const (ggA P D)).mul (isPoly_xA P D)).mul (isPoly_raising_constant P D)).mul (isPoly_lowering_constant P D))).add ((((IsPoly.const (ggA P D)).mul (isPoly_raising_constant P D)).mul (IsPoly.const (ggiA P D))).mul (is …`.
-/
theorem isPoly_upper_left_entry (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] : IsPoly (t11 P D) :=
  (((((IsPoly.const (ggiA P D)).mul (isPoly_w P D)).add
    ((((IsPoly.const (ggA P D)).mul (isPoly_xA P D)).mul (isPoly_raising_constant P D)).mul (isPoly_lowering_constant P D))).add
    ((((IsPoly.const (ggA P D)).mul (isPoly_raising_constant P D)).mul (IsPoly.const (ggiA P D))).mul (isPoly_S21 P D))).add
    ((isPoly_S12 P D).mul (isPoly_lowering_constant P D))).add ((IsPoly.const (ggiA P D)).mul (isPoly_quartic_sum P D))

noncomputable def badSet (P : Par) : Finset ℂ :=
  (Finset.univ : Finset (Ty P)).biUnion fun π => (Icc 1 (P.k - 1)).biUnion fun i =>
    {-(rho P π i : ℂ), -(rho P π i : ℂ) - 1, -(rho P π i : ℂ) - 2}

/- English proof (translation)
Unfold `xC`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i hi h0`. Apply `hY` to reduce the goal to its premises. Simplify using `only [badSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]`.

Use `⟨π, i, hi, ?_⟩` and prove the remaining obligations. Break down `hc with rfl | rfl | rfl` into its components or cases. Use `left`. Take the linear combination `h0`. Use `right`.

Use `left`. Take the linear combination `h0`. Use `right`. Use `right`. Take the linear combination `h0`.
-/
theorem good_of (P : Par) (Y : ℂ) (hY : Y ∉ badSet P) (c : ℂ) (hc : c = 0 ∨ c = 1 ∨ c = 2) (π : Ty P) :
    xC P π (Y + c) ≠ 0 := by
  unfold xC
  rw [Finset.prod_ne_zero_iff]
  intro i hi h0
  apply hY
  simp only [badSet, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  refine ⟨π, i, hi, ?_⟩
  rcases hc with rfl | rfl | rfl
  · left; linear_combination h0
  · right; left; linear_combination h0
  · right; right; linear_combination h0

/- English proof (translation)
Establish `hg : ∀ Z, Z ∉ (↑(badSet P) : Set ℂ) → Det8 P D Z`. Introduce `Z hZ`. Establish `hZ' : Z ∉ badSet P` using `by simpa using hZ`. Use `det_eight_at_good_point hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P D hP Z ?_ ?_ ?_` and prove the remaining obligations. Introduce `π`.

Use `good_of P Z hZ' 0 (Or.inl rfl) π` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis. Conclude with `good_of P Z hZ' 1 (Or.inr (Or.inl rfl))`. Introduce `π`. Use `good_of P Z hZ' 2 (Or.inr (Or.inr rfl)) π` as an intermediate fact.

Rewrite `this` using `[show Z + 2 = Z + 1 + 1 by ring]`. Then use the resulting hypothesis. Establish `hfin : (↑(badSet P) : Set ℂ).Finite` using `Finset.finite_toSet _`. Apply the tactic sequence `have p11 := isPoly_upper_left_entry P D`. Apply the tactic sequence `have p12 := isPoly_upper_right_entry P D`. Establish `p21` using `isPoly_t21 P D`.

Apply the tactic sequence `have p22 := isPoly_diagonal_entry P D`. Establish `s11` using `p11.shift 1`. Establish `s12` using `p12.shift 1`. Establish `s21` using `p21.shift 1`. Establish `s22` using `p22.shift 1`.

Establish `pq` using `isPoly_q P D`. Establish `p0 : IsPoly (fun _ : ℂ => (0 : A P D))` using `IsPoly.const 0`. Conclude with `⟨((s11.mul p21).sub (s21.mul p11)).ext p0 hfin (fun Z hZ => (hg Z hZ).1) Y, ((s11.mul p22).sub (s21.mul p12)).ext pq hfin (fun Z hZ => (hg Z hZ).2.1) Y, ((s12.mul p21).sub (s22.mul p11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.1) Y, ((s12.mul p22).sub (s22.mul p12)).ext p0 hfi …`.
-/
theorem det8 (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal)
    (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (hP : P.OK) (Y : ℂ) : Det8 P D Y := by
  have hg : ∀ Z, Z ∉ (↑(badSet P) : Set ℂ) → Det8 P D Z := by
    intro Z hZ
    have hZ' : Z ∉ badSet P := by simpa using hZ
    refine det_eight_at_good_point hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P D hP Z ?_ ?_ ?_
    · intro π; have := good_of P Z hZ' 0 (Or.inl rfl) π; rwa [add_zero] at this
    · exact good_of P Z hZ' 1 (Or.inr (Or.inl rfl))
    · intro π; have := good_of P Z hZ' 2 (Or.inr (Or.inr rfl)) π
      rwa [show Z + 2 = Z + 1 + 1 by ring] at this
  have hfin : (↑(badSet P) : Set ℂ).Finite := Finset.finite_toSet _
  have p11 := isPoly_upper_left_entry P D
  have p12 := isPoly_upper_right_entry P D
  have p21 := isPoly_t21 P D
  have p22 := isPoly_diagonal_entry P D
  have s11 := p11.shift 1
  have s12 := p12.shift 1
  have s21 := p21.shift 1
  have s22 := p22.shift 1
  have pq := isPoly_q P D
  have p0 : IsPoly (fun _ : ℂ => (0 : A P D)) := IsPoly.const 0
  exact ⟨((s11.mul p21).sub (s21.mul p11)).ext p0 hfin (fun Z hZ => (hg Z hZ).1) Y,
    ((s11.mul p22).sub (s21.mul p12)).ext pq hfin (fun Z hZ => (hg Z hZ).2.1) Y,
    ((s12.mul p21).sub (s22.mul p11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.1) Y,
    ((s12.mul p22).sub (s22.mul p12)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.1) Y,
    ((p11.mul s12).sub (p12.mul s11)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.2.1) Y,
    ((p11.mul s22).sub (p12.mul s21)).ext pq hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.1) Y,
    ((p21.mul s12).sub (p22.mul s11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.2.1) Y,
    ((p21.mul s22).sub (p22.mul s21)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.2.2) Y⟩

/- English proof (translation)
Introduce `P D _ hP Y`. Take `⟨e1, e2, e3, e4, e5, e6, e7, e8⟩` from `det8 hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P D hP Y`. Conclude with `isSymplectic_of_eight_relations _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8`.
-/
theorem qQDet_of (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal) :
    QQDet := by
  intro P D _ hP Y
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := det8 hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P D hP Y
  exact isSymplectic_of_eight_relations _ _ _ _ _ _ _ _ _ e1 e2 e3 e4 e5 e6 e7 e8

end PartD

end Formalism.FourierDecayAlt.P.MAx1.D7

namespace Formalism.FourierDecayAlt.P.MAx1

/- English proof (translation)
The claim follows from `D7.qQDet_of sSScalar sSShift rho_raise levFns levNab levNabs starGens nabSS sSNorm sSMixed curvature qQNormal`.
-/
theorem qQDet : QQDet :=
  D7.qQDet_of sSScalar sSShift rho_raise levFns levNab levNabs starGens nabSS sSNorm sSMixed curvature qQNormal

/- English proof (translation)
The claim follows from `D7.lower_left_commute_of_laws sSScalar sSShift sSComm nabSS levNab levFns rho_raise`.
-/
theorem lower_left_commute : T21Commute :=
  D7.lower_left_commute_of_laws sSScalar sSShift sSComm nabSS levNab levFns rho_raise

end Formalism.FourierDecayAlt.P.MAx1

end

section

open  Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt Matrix Finset
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.MAx1.WeylSymmetry

noncomputable section

section Abstract

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [E1, Matrix.of_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem kronecker_E1_smul (s : ℂ) (M : M2 A) : E1 (s • M) = s • E1 M := by
  ext a b
  simp only [E1, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [E2, Matrix.of_apply, Matrix.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eval_two_smul (s : ℂ) (M : M2 A) : E2 (s • M) = s • E2 M := by
  ext a b
  simp only [E2, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `⟨fun Y hY => ?_, fun Y Y' => ?_, fun Y => ⟨?_, ?_⟩, h.q_real⟩` and prove the remaining obligations. Use `show (s • QQ Y)ᴴ = s • QQ Y`. Rewrite using `[Matrix.conjTranspose_smul, hs', h.herm Y hY]`. Simplify using `only [kronecker_E1_smul, eval_two_smul, mul_smul_comm, smul_mul_assoc]`. Rewrite using `[h.rtt Y Y']`.

Simplify using `only [Matrix.transpose_smul, mul_smul_comm, smul_mul_assoc, smul_smul, hs, one_smul]`. Conclude with `(h.det Y).1`. Simplify using `only [Matrix.transpose_smul, mul_smul_comm, smul_mul_assoc, smul_smul, hs, one_smul]`. Conclude with `(h.det Y).2`.
-/
theorem isStart_smul (QQ : ℂ → M2 A) (q : ℂ → ℂ) (s : ℂ) (hs : s * s = 1) (hs' : star s = s)
    (h : IsStart QQ q) : IsStart (fun Y => s • QQ Y) q := by
  refine ⟨fun Y hY => ?_, fun Y Y' => ?_, fun Y => ⟨?_, ?_⟩, h.q_real⟩
  · show (s • QQ Y)ᴴ = s • QQ Y
    rw [Matrix.conjTranspose_smul, hs', h.herm Y hY]
  · simp only [kronecker_E1_smul, eval_two_smul, mul_smul_comm, smul_mul_assoc]
    rw [h.rtt Y Y']
  · simp only [Matrix.transpose_smul, mul_smul_comm, smul_mul_assoc, smul_smul, hs, one_smul]
    exact (h.det Y).1
  · simp only [Matrix.transpose_smul, mul_smul_comm, smul_mul_assoc, smul_smul, hs, one_smul]
    exact (h.det Y).2

def sStar (σ : Site A) : Site A := ⟨star σ.p, -star σ.ci, -star σ.c⟩

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;>`. Simplify using `[Ts, Tm, sStar, Matrix.conjTranspose_apply, ← algebraMap_star_comm]`.
-/
theorem Ts_conj (σ : Site A) (Y : ℂ) : (Ts σ (star Y))ᴴ = Ts (sStar σ) Y := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Ts, Tm, sStar, Matrix.conjTranspose_apply, ← algebraMap_star_comm]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `e : ci * (p * c) * ci = ci * (c * p + c) * ci` using `by rw [h3]`. Establish `l : ci * (p * c) * ci = ci * p` using `by rw [mul_assoc, mul_assoc, h1, mul_one]`. Establish `r : ci * (c * p + c) * ci = p * ci + ci`. Rewrite using `[mul_add, ← mul_assoc, h2, one_mul, add_mul, one_mul]`.

Rewrite `e` using `[l, r]`. Rewrite using `[e]`. Normalize the expressions using the abelian group laws.
-/
theorem weyl_ci {p c ci : A} (h : WeylRel p c ci) : p * ci = ci * p - ci := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : ci * (p * c) * ci = ci * (c * p + c) * ci := by rw [h3]
  have l : ci * (p * c) * ci = ci * p := by rw [mul_assoc, mul_assoc, h1, mul_one]
  have r : ci * (c * p + c) * ci = p * ci + ci := by
    rw [mul_add, ← mul_assoc, h2, one_mul, add_mul, one_mul]
  rw [l, r] at e
  rw [e]; abel

/- English proof (translation)
Establish `h4` using `weyl_ci h`. Take `⟨h1, h2, h3⟩` from `h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show -star σ.ci * -star σ.c = 1`. Rewrite using `[neg_mul_neg, ← star_mul, h1, star_one]`.

Use `show -star σ.c * -star σ.ci = 1`. Rewrite using `[neg_mul_neg, ← star_mul, h2, star_one]`. Use `show star σ.p * -star σ.ci = -star σ.ci * star σ.p + -star σ.ci`. Rewrite using `[mul_neg, neg_mul, ← star_mul, ← star_mul, h4, star_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem weyl_star {σ : Site A} (h : WeylRel σ.p σ.c σ.ci) :
    WeylRel (sStar σ).p (sStar σ).c (sStar σ).ci := by
  have h4 := weyl_ci h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show -star σ.ci * -star σ.c = 1
    rw [neg_mul_neg, ← star_mul, h1, star_one]
  · show -star σ.c * -star σ.ci = 1
    rw [neg_mul_neg, ← star_mul, h2, star_one]
  · show star σ.p * -star σ.ci = -star σ.ci * star σ.p + -star σ.ci
    rw [mul_neg, neg_mul, ← star_mul, ← star_mul, h4, star_sub]; abel

/- English proof (translation)
Introduce `Y Y'` and use `Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' h`.
-/
theorem isRTT_Tm {p c ci : A} (h : WeylRel p c ci) : IsRTT (fun Y : ℂ => Tm Y p c ci) :=
  fun Y Y' => Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' h

/- English proof (translation)
Introduce `Y`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, one_smul]`. Conclude with `Formalism.YangianSpanCharacter.P.transposeSymplecticShift ℂ A p c ci Y h`. Rewrite using `[map_one, one_smul]`.

Take `⟨h1, h2, h3⟩` from `h`. Establish `hc : algebraMap ℂ A Y * c = c * algebraMap ℂ A Y` using `Algebra.commutes _ _`. Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, h3, hc]`.

Normalize the expressions using the abelian group laws. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h1]`. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h2]`. Simplify using `[Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem isDet_Tm {p c ci : A} (h : WeylRel p c ci) : IsDet (fun Y : ℂ => Tm Y p c ci) (fun _ => 1) := by
  intro Y
  refine ⟨?_, ?_⟩
  · rw [map_one, one_smul]
    exact Formalism.YangianSpanCharacter.P.transposeSymplecticShift ℂ A p c ci Y h
  · rw [map_one, one_smul]
    obtain ⟨h1, h2, h3⟩ := h
    have hc : algebraMap ℂ A Y * c = c * algebraMap ℂ A Y := Algebra.commutes _ _
    ext a b
    fin_cases a <;> fin_cases b
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, add_mul, mul_add, h3, hc]
      abel
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h1]
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two, h2]
    · simp [Tm, Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show Commute x (algebraMap ℂ A Y + σ.p)`. Conclude with `((Algebra.commute_algebraMap_right Y x)).add_right hp`. Use `show Commute x (-σ.c)`. Conclude with `hc.neg_right`.

Conclude with `hci`. Conclude with `Commute.zero_right x`.
-/
theorem Ts_comm (σ : Site A) (x : A) (hp : Commute x σ.p) (hc : Commute x σ.c) (hci : Commute x σ.ci)
    (Y : ℂ) (a b : Fin 2) : Commute x (Ts σ Y a b) := by
  fin_cases a <;> fin_cases b
  · show Commute x (algebraMap ℂ A Y + σ.p)
    exact ((Algebra.commute_algebraMap_right Y x)).add_right hp
  · show Commute x (-σ.c)
    exact hc.neg_right
  · exact hci
  · exact Commute.zero_right x

/- English proof (translation)
Take `⟨hW, hH⟩` from `hσ`. Establish `mp : σ.p ∈ hol σ` using `by simp [hol]`. Establish `mc : σ.c ∈ hol σ` using `by simp [hol]`. Establish `mci : σ.ci ∈ hol σ` using `by simp [hol]`. Establish `c1 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) QQ`.

Introduce `Y Y' i j k l`. Use `(Ts_comm (sStar σ) (QQ Y' k l) ?_ ?_ ?_ Y i j).symm` and prove the remaining obligations. Conclude with `hc Y' k l (star σ.p) (Or.inr (by rw [star_star]; exact mp))`. Conclude with `(hc Y' k l (star σ.ci) (Or.inr (by rw [star_star]; exact mci))).neg_right`. Conclude with `(hc Y' k l (star σ.c) (Or.inr (by rw [star_star]; exact mc))).neg_right`.

Establish `c2 : EntriesCommute QQ (fun Y : ℂ => Ts σ Y)`. Introduce `Y Y' i j k l`. Conclude with `Ts_comm σ (QQ Y i j) (hc Y i j _ (Or.inl mp)) (hc Y i j _ (Or.inl mc)) (hc Y i j _ (Or.inl mci)) Y' k l`. Establish `c3 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) (fun Y : ℂ => Ts σ Y)`. Introduce `Y Y' i j k l`.

Establish `key : ∀ x ∈ hol σ, Commute (Ts (sStar σ) Y i j) x` using `fun x hx => (Ts_comm (sStar σ) x (hH x hx _ mp) (hH x hx _ mci).neg_right (hH x hx _ mc).neg_right Y i j).symm`. Conclude with `Ts_comm σ _ (key _ mp) (key _ mc) (key _ mci) Y' k l`. Establish `hF` using `Formalism.FourierDecayAlt.P.W.wordFusion_list (R := ℂ) (B := A) [(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] (by`. Introduce `x hx`. Simplify using `only [List.mem_cons, List.not_mem_nil, or_false] at hx`.

Break down `hx with rfl | rfl | rfl` into its components or cases. Conclude with `⟨isRTT_Tm (weyl_star hW), isDet_Tm (weyl_star hW)⟩`. Conclude with `⟨h.rtt, h.det⟩`. Conclude with `⟨isRTT_Tm hW, isDet_Tm hW⟩)`. Use the proof step `(by`.

Simplify using `only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]`. Conclude with `⟨⟨c1, c3⟩, c2⟩)`. Establish `e1 : (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) = fun Y => (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] : List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.1 Y)).prod`. Use function extensionality and compare the values at `Y`. Rewrite using `[Ts_conj]`.

Simplify using `[mul_assoc]`. Establish `e2 : q = fun Y => (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] : List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.2 Y)).prod`. Use function extensionality and compare the values at `Y`. Simplify using the standard rewrite rules. Use `⟨fun Y hY => ?_, ?_, ?_, h.q_real⟩` and prove the remaining obligations.

Simplify using `only [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h.herm Y hY, mul_assoc]`. Rewrite using `[e1]`. Conclude with `hF.1`. Rewrite using `[e1]`. Use `hF.2` as an intermediate fact.

Rewrite `this` using `[← e2]`. Then use the resulting hypothesis.
-/
theorem isStart_step (σ : Site A) (QQ : ℂ → M2 A) (q : ℂ → ℂ) (hσ : IsSite σ)
    (hc : QQCommutes QQ σ) (h : IsStart QQ q) :
    IsStart (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) q := by
  obtain ⟨hW, hH⟩ := hσ
  have mp : σ.p ∈ hol σ := by simp [hol]
  have mc : σ.c ∈ hol σ := by simp [hol]
  have mci : σ.ci ∈ hol σ := by simp [hol]
  have c1 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) QQ := by
    intro Y Y' i j k l
    refine (Ts_comm (sStar σ) (QQ Y' k l) ?_ ?_ ?_ Y i j).symm
    · exact hc Y' k l (star σ.p) (Or.inr (by rw [star_star]; exact mp))
    · exact (hc Y' k l (star σ.ci) (Or.inr (by rw [star_star]; exact mci))).neg_right
    · exact (hc Y' k l (star σ.c) (Or.inr (by rw [star_star]; exact mc))).neg_right
  have c2 : EntriesCommute QQ (fun Y : ℂ => Ts σ Y) := by
    intro Y Y' i j k l
    exact Ts_comm σ (QQ Y i j) (hc Y i j _ (Or.inl mp)) (hc Y i j _ (Or.inl mc)) (hc Y i j _ (Or.inl mci)) Y' k l
  have c3 : EntriesCommute (fun Y : ℂ => Ts (sStar σ) Y) (fun Y : ℂ => Ts σ Y) := by
    intro Y Y' i j k l
    have key : ∀ x ∈ hol σ, Commute (Ts (sStar σ) Y i j) x := fun x hx =>
      (Ts_comm (sStar σ) x (hH x hx _ mp) (hH x hx _ mci).neg_right (hH x hx _ mc).neg_right Y i j).symm
    exact Ts_comm σ _ (key _ mp) (key _ mc) (key _ mci) Y' k l
  have hF := Formalism.FourierDecayAlt.P.W.wordFusion_list (R := ℂ) (B := A)
    [(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)]
    (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨isRTT_Tm (weyl_star hW), isDet_Tm (weyl_star hW)⟩
      · exact ⟨h.rtt, h.det⟩
      · exact ⟨isRTT_Tm hW, isDet_Tm hW⟩)
    (by
      simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
        IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
      exact ⟨⟨c1, c3⟩, c2⟩)
  have e1 : (fun Y => (Ts σ (star Y))ᴴ * QQ Y * Ts σ Y) = fun Y =>
      (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] :
        List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.1 Y)).prod := by
    funext Y
    rw [Ts_conj]
    simp [mul_assoc]
  have e2 : q = fun Y =>
      (([(fun Y : ℂ => Ts (sStar σ) Y, fun _ => 1), (QQ, q), (fun Y : ℂ => Ts σ Y, fun _ => 1)] :
        List ((ℂ → Matrix (Fin 2) (Fin 2) A) × (ℂ → ℂ))).map (fun x => x.2 Y)).prod := by
    funext Y
    simp
  refine ⟨fun Y hY => ?_, ?_, ?_, h.q_real⟩
  · simp only [hY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, h.herm Y hY, mul_assoc]
  · rw [e1]; exact hF.1
  · rw [e1]
    have := hF.2
    rwa [← e2] at this

end Abstract

section Lev

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)

def G (l : Fin r) : Set A := {L.p l, L.c l, L.ci l, -L.pb l, L.cb l, L.cbi l}

/- English proof (translation)
Establish `h'` using `h.symm`. Establish `pc : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.c b)` using `fun a b hab => by`. Use `L.p_c a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, add_zero]`. Then use the resulting hypothesis. Establish `pci : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.ci b)` using `fun a b hab => by`.

Use `L.p_ci a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, sub_zero]`. Then use the resulting hypothesis. Establish `pbcb : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cb b)` using `fun a b hab => by`. Use `L.pb_cb a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, add_zero]`. Then use the resulting hypothesis.

Establish `pbcbi : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cbi b)` using `fun a b hab => by`. Use `L.pb_cbi a b` as an intermediate fact. Rewrite `this` using `[if_neg hab, sub_zero]`. Then use the resulting hypothesis. Introduce `x hx y hy`. Simplify using `only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`.

Apply the tactic sequence `rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `(try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>`. Use `first`. Consider the case `exact L.p_p _ _ | exact L.p_pb _ _ | exact (L.p_pb _ _).symm | exact L.pb_pb _ _`.

Consider the case `exact pc _ _ h | exact (pc _ _ h').symm | exact pci _ _ h | exact (pci _ _ h').symm`. Consider the case `exact pbcb _ _ h | exact (pbcb _ _ h').symm | exact pbcbi _ _ h | exact (pbcbi _ _ h').symm`. Consider the case `exact L.p_cb _ _ | exact (L.p_cb _ _).symm | exact L.p_cbi _ _ | exact (L.p_cbi _ _).symm`. Consider the case `exact L.pb_c _ _ | exact (L.pb_c _ _).symm | exact L.pb_ci _ _ | exact (L.pb_ci _ _).symm`. Consider the case `exact L.fns_comm _ (by simp) _ (by simp)`.
-/
theorem G_comm_ne (l m : Fin r) (h : l ≠ m) : ∀ x ∈ G L l, ∀ y ∈ G L m, Commute x y := by
  have h' := h.symm
  have pc : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.c b) := fun a b hab => by
    have := L.p_c a b; rwa [if_neg hab, add_zero] at this
  have pci : ∀ a b : Fin r, a ≠ b → Commute (L.p a) (L.ci b) := fun a b hab => by
    have := L.p_ci a b; rwa [if_neg hab, sub_zero] at this
  have pbcb : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cb b) := fun a b hab => by
    have := L.pb_cb a b; rwa [if_neg hab, add_zero] at this
  have pbcbi : ∀ a b : Fin r, a ≠ b → Commute (L.pb a) (L.cbi b) := fun a b hab => by
    have := L.pb_cbi a b; rwa [if_neg hab, sub_zero] at this
  intro x hx y hy
  simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_p _ _ | exact L.p_pb _ _ | exact (L.p_pb _ _).symm | exact L.pb_pb _ _
    | exact pc _ _ h | exact (pc _ _ h').symm | exact pci _ _ h | exact (pci _ _ h').symm
    | exact pbcb _ _ h | exact (pbcb _ _ h').symm | exact pbcbi _ _ h | exact (pbcbi _ _ h').symm
    | exact L.p_cb _ _ | exact (L.p_cb _ _).symm | exact L.p_cbi _ _ | exact (L.p_cbi _ _).symm
    | exact L.pb_c _ _ | exact (L.pb_c _ _).symm | exact L.pb_ci _ _ | exact (L.pb_ci _ _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)

/- English proof (translation)
Introduce `x hx y hy`. Simplify using `only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>`. Apply the tactic sequence `(try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>`.

Use `first`. Consider the case `exact L.p_ζ _ | exact L.p_ζb _ | exact L.p_GG _ | exact L.p_GGi _ | exact L.p_nab _ | exact L.p_nabs _`. Consider the case `exact L.pb_ζ _ | exact L.pb_ζb _ | exact L.pb_GG _ | exact L.pb_GGi _ | exact L.pb_nab _`. Consider the case `exact L.pb_nabs _`. Consider the case `exact (L.nab_c _).symm | exact (L.nab_ci _).symm | exact (L.nab_cb _).symm | exact (L.nab_cbi _).symm`.

Consider the case `exact (L.nabs_c _).symm | exact (L.nabs_ci _).symm | exact (L.nabs_cb _).symm`. Consider the case `exact (L.nabs_cbi _).symm`. Consider the case `exact L.fns_comm _ (by simp) _ (by simp)`.
-/
theorem gamma_family_commute_generators (l : Fin r) : ∀ x ∈ G L l,
    ∀ y ∈ ({L.ζ, L.ζb, L.GG, L.GGi, L.nab, L.nabs} : Set A), Commute x y := by
  intro x hx y hy
  simp only [G, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_ζ _ | exact L.p_ζb _ | exact L.p_GG _ | exact L.p_GGi _ | exact L.p_nab _ | exact L.p_nabs _
    | exact L.pb_ζ _ | exact L.pb_ζb _ | exact L.pb_GG _ | exact L.pb_GGi _ | exact L.pb_nab _
    | exact L.pb_nabs _
    | exact (L.nab_c _).symm | exact (L.nab_ci _).symm | exact (L.nab_cb _).symm | exact (L.nab_cbi _).symm
    | exact (L.nabs_c _).symm | exact (L.nabs_ci _).symm | exact (L.nabs_cb _).symm
    | exact (L.nabs_cbi _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)

/- English proof (translation)
Introduce `x hx y hy`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy`. Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;> first`. Consider the case `exact L.p_pb _ _ | exact L.p_cb _ _ | exact L.p_cbi _ _`. Consider the case `exact (L.pb_c _ _).symm | exact (L.pb_ci _ _).symm`.

Consider the case `exact L.fns_comm _ (by simp) _ (by simp)`.
-/
theorem hol_comm (l : Fin r) : ∀ x ∈ ({L.p l, L.c l, L.ci l} : Set A),
    ∀ y ∈ ({-L.pb l, L.cb l, L.cbi l} : Set A), Commute x y := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    (try simp only [Commute.neg_left_iff, Commute.neg_right_iff]) <;>
    first
    | exact L.p_pb _ _ | exact L.p_cb _ _ | exact L.p_cbi _ _
    | exact (L.pb_c _ _).symm | exact (L.pb_ci _ _).symm
    | exact L.fns_comm _ (by simp) _ (by simp)

/- English proof (translation)
Establish `c1 : L.GGi * L.ζ = L.ζ * L.GGi` using `L.fns_comm _ (by simp) _ (by simp)`. Establish `c3 : L.ζb * L.GGi = L.GGi * L.ζb` using `L.fns_comm _ (by simp) _ (by simp)`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = L.ζb * ((L.ζi * L.ζ) * L.GGi) * L.ζbi := by rw [c1]; simp only [mul_assoc]`.

Use `_ = L.GGi * (L.ζb * L.ζbi) := by rw [L.ζi_ζ, one_mul, c3, mul_assoc]`. Use `_ = L.GGi := by rw [L.ζb_ζbi, mul_one]`.
-/
theorem fn_cancel : L.ζb * L.ζi * L.GGi * (L.ζ * L.ζbi) = L.GGi := by
  have c1 : L.GGi * L.ζ = L.ζ * L.GGi := L.fns_comm _ (by simp) _ (by simp)
  have c3 : L.ζb * L.GGi = L.GGi * L.ζb := L.fns_comm _ (by simp) _ (by simp)
  calc L.ζb * L.ζi * L.GGi * (L.ζ * L.ζbi) = L.ζb * (L.ζi * (L.GGi * L.ζ)) * L.ζbi := by
        simp only [mul_assoc]
    _ = L.ζb * ((L.ζi * L.ζ) * L.GGi) * L.ζbi := by rw [c1]; simp only [mul_assoc]
    _ = L.GGi * (L.ζb * L.ζbi) := by rw [L.ζi_ζ, one_mul, c3, mul_assoc]
    _ = L.GGi := by rw [L.ζb_ζbi, mul_one]

end Lev

/- English proof (translation)
Unfold `sgn`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) : sgn P l * sgn P l = 1 := by
  unfold sgn
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/- English proof (translation)
Unfold `sgn`. Simplify using the standard rewrite rules.
-/
theorem sgn_star (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) : star (sgn P l) = sgn P l := by
  unfold sgn
  simp

/- English proof (translation)
Establish `hY' : (starRingEnd ℂ) Y = Y` using `hY`. Establish `h2 : (starRingEnd ℂ) (2 : ℂ) = 2` using `map_ofNat _ 2`. Use `show (starRingEnd ℂ) (qC P Y) = qC P Y`. Simplify using `[qC, map_prod, hY', h2]`.
-/
theorem qC_real (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) (hY : star Y = Y) : star (qC P Y) = qC P Y := by
  have hY' : (starRingEnd ℂ) Y = Y := hY
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  show (starRingEnd ℂ) (qC P Y) = qC P Y
  simp [qC, map_prod, hY', h2]

/- English proof (translation)
Establish `hY' : (starRingEnd ℂ) Y = Y` using `hY`. Use `show (starRingEnd ℂ) (x0 P l π Y) = x0 P l π Y`. Simplify using `[x0, map_prod, hY']`.
-/
theorem coordinate_real (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (π : Ty P) (Y : ℂ) (hY : star Y = Y) :
    star (x0 P l π Y) = x0 P l π Y := by
  have hY' : (starRingEnd ℂ) Y = Y := hY
  show (starRingEnd ℂ) (x0 P l π Y) = x0 P l π Y
  simp [x0, map_prod, hY']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kap_eq (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) :
    kap P D f = Matrix.diagonal fun π => algebraMap ℂ (D.Pr) (f π) := rfl

/- English proof (translation)
Use `show kap P D f * _ = _ * kap P D f`. Rewrite using `[kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Conclude with `Algebra.commutes _ _`.
-/
theorem kap_comm_diag (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) (d : Ty P → D.Pr) :
    Commute (kap P D f) (Matrix.diagonal d) := by
  show kap P D f * _ = _ * kap P D f
  rw [kap_eq, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext π
  exact Algebra.commutes _ _

/- English proof (translation)
The claim follows from `kap_comm_diag P D f _`.
-/
theorem kap_comm_sc (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) (w : D.Pr) : Commute (kap P D f) (sc P D w) :=
  kap_comm_diag P D f _

/- English proof (translation)
Use `show _ * _ = _ * _`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.
-/
theorem kap_comm_kap (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f g : Ty P → ℂ) : Commute (kap P D f) (kap P D g) := by
  show _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Rewrite using `[kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `π`. Simplify using `[← algebraMap_star_comm]`.
-/
theorem star_kap (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (f : Ty P → ℂ) : star (kap P D f) = kap P D (star f) := by
  rw [kap_eq, kap_eq, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  congr 1
  funext π
  simp [← algebraMap_star_comm]

/- English proof (translation)
Establish `h : (fun π => x0 P l π Y) = sgn P l • (fun π => xC P π Y)`. Use extensionality with `π`. Simplify using `[x0, sgn, xC]`. Rewrite using `[h, map_smul]`. Both sides reduce to the same expression.
-/
theorem kappa_sign_coordinate (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (Y : ℂ) : (kap P D fun π => x0 P l π Y) = sgn P l • xA P D Y := by
  have h : (fun π => x0 P l π Y) = sgn P l • (fun π => xC P π Y) := by
    ext π; simp [x0, sgn, xC]
  rw [h, map_smul]; rfl

/- English proof (translation)
Introduce `P D _ l w`. Use `show SS P D l * sc P D w = sc P D w * SS P D l`. Use extensionality with `π' π`. Simplify using `only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `(Algebra.commutes _ _)`. Simplify using the standard rewrite rules.
-/
theorem ssScalar : SSScalar := by
  intro P D _ l w
  show SS P D l * sc P D w = sc P D w * SS P D l
  ext π' π
  simp only [sc, Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, SS, Matrix.of_apply]
  split_ifs
  · exact (Algebra.commutes _ _)
  · simp

/- English proof (translation)
Rewrite using `[Finset.mul_sum, weightedSumBis]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, xA, ← map_mul]`. Use `hSh P D j _ _ fun π π' hU => ?_` and prove the remaining obligations. Establish `hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1)` using `Finset.singleton_subset_iff.2 hj`.

Establish `h1 : xC P π' Y = xEx P {j} π' Y * (Y + (rho P π' j : ℂ))`. Rewrite using `[xC, xEx, ← Finset.prod_sdiff hsub, Finset.prod_singleton]`. Establish `h2 : Y + (rho P π' j : ℂ) ≠ 0` using `fun h0 => hY π' (by rw [h1, h0, mul_zero])`. Establish `h3 : xEx P {j} π' Y = xEx P {j} π Y`. Unfold `xEx`.

Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_sdiff, Finset.mem_singleton]`. Rewrite using `[hRho P j π π' hU i hi.1, if_neg hi.2, add_zero]`. Use `show xC P π' Y * (Y + (rho P π' j : ℂ))⁻¹ = xEx P {j} π Y`. Rewrite using `[h1, mul_assoc, mul_inv_cancel₀ h2, mul_one, h3]`.
-/
theorem low_sum (hSh : SSShift) (hRho : RhoUp) (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (Y : ℂ) (hY : ∀ π, xC P π Y ≠ 0) :
    xA P D Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j = weightedSumBis P D Y := by
  rw [Finset.mul_sum, weightedSumBis]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← mul_assoc, xA, ← map_mul]
  refine hSh P D j _ _ fun π π' hU => ?_
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) := Finset.singleton_subset_iff.2 hj
  have h1 : xC P π' Y = xEx P {j} π' Y * (Y + (rho P π' j : ℂ)) := by
    rw [xC, xEx, ← Finset.prod_sdiff hsub, Finset.prod_singleton]
  have h2 : Y + (rho P π' j : ℂ) ≠ 0 := fun h0 => hY π' (by rw [h1, h0, mul_zero])
  have h3 : xEx P {j} π' Y = xEx P {j} π Y := by
    unfold xEx
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    rw [hRho P j π π' hU i hi.1, if_neg hi.2, add_zero]
  show xC P π' Y * (Y + (rho P π' j : ℂ))⁻¹ = xEx P {j} π Y
  rw [h1, mul_assoc, mul_inv_cancel₀ h2, mul_one, h3]

/- English proof (translation)
Introduce `P D _ hP l L hL`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩` from `hL`. Establish `hzf : ∀ g ∈ zfns L, ∃ w, g = sc P D w`. Introduce `g hg`. Simplify using `only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg`.

Break down `hg with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `⟨D.zP, hz⟩`. Conclude with `⟨D.ziP, hzi⟩`. Conclude with `⟨D.zbP, hzb⟩`. Conclude with `⟨D.zbiP, hzbi⟩`.

Conclude with `⟨D.ggP P.TT, hgg⟩`. Conclude with `⟨D.ggiP P.TT, hggi⟩`. Use `⟨hS P D hP l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `Y Y' show Commute (sgn P l • t21 P D Y) (sgn P l • t21 P D Y')`. Conclude with `((hT P D hP Y Y').smul_left _).smul_right _`.

Introduce `Y hY`. Establish `hne : ∀ π, x0 P l π Y ≠ 0` using `fun π => mul_ne_zero (pow_ne_zero _ (by norm_num)) (hY π)`. Establish `h1 : ((fun π => x0 P l π Y) * fun π => (x0 P l π Y)⁻¹) = (1 : Ty P → ℂ)`. Use function extensionality and compare the values at `π`. Conclude with `mul_inv_cancel₀ (hne π)`.

Establish `h2 : ((fun π => (x0 P l π Y)⁻¹) * fun π => x0 P l π Y) = (1 : Ty P → ℂ)`. Use function extensionality and compare the values at `π`. Conclude with `inv_mul_cancel₀ (hne π)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show (kap P D fun π => x0 P l π Y) * (kap P D fun π => (x0 P l π Y)⁻¹) = 1`.

Rewrite using `[← map_mul, h1, map_one]`. Use `show (kap P D fun π => (x0 P l π Y)⁻¹) * (kap P D fun π => x0 P l π Y) = 1`. Rewrite using `[← map_mul, h2, map_one]`. Introduce `Y Y'`. Conclude with `kap_comm_kap P D _ _`.

Introduce `Y g hg`. Take `⟨w, rfl⟩` from `hzf g hg`. Conclude with `kap_comm_sc P D _ w`. Introduce `Y`. Rewrite using `[hnab]`.

Conclude with `kap_comm_diag P D _ _`. Introduce `Y hY show star (kap P D fun π => x0 P l π Y) = kap P D fun π => x0 P l π Y`. Rewrite using `[star_kap]`. Use `congr 1`. Use function extensionality and compare the values at `π`.

Conclude with `coordinate_real P D l π Y hY`. Introduce `Y g hg`. Establish `h1 : Commute (zA P D) g`. Rewrite using `[← hz]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)`. Establish `h2 : Commute (zbiA P D) g`.

Rewrite using `[← hzbi]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)`. Establish `h3 : Commute (∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j) g`. Take `⟨w, hw⟩` from `hzf g hg`. Rewrite using `[hw]`. Conclude with `Commute.sum_left _ _ _ fun j _ => (kap_comm_sc P D _ w).mul_left (hSc P D j w)`.

Conclude with `(h1.mul_left h2).mul_left h3`. Introduce `Y show sgn P l • (ggA P D * xA P D Y) = L.GG * kap P D (fun π => x0 P l π Y)`. Rewrite using `[kappa_sign_coordinate, mul_smul_comm, hgg]`. Introduce `Y hY`. Establish `hl0 : L.l0 Y = l0A P D Y` using `by simp only [LevelData.l0, l0A, hnab, hzb, hggi]`.

Establish `hcan` using `fn_cancel L`. Establish `hgi` using `L.GG_GGi`. Rewrite `hcan` using `[hzb, hzi, hggi, hz, hzbi]`. Rewrite `hgi` using `[hgg, hggi]`. Establish `hcx : ggA P D * xA P D Y = xA P D Y * ggA P D` using `(kap_comm_sc P D _ _).eq.symm`.

Use `show sgn P l • (ggA P D * xA P D Y * l0A P D Y + weightedSumBis P D Y) = L.GG * (kap P D fun π => x0 P l π Y) * (L.l0 Y + L.ζb * L.ζi * L.GGi * eeA P D Y)`. Rewrite using `[hl0, kappa_sign_coordinate, hgg, hzb, hzi, hggi, ← low_sum hSh hRho P D Y hY, eeA, ← mul_assoc _ (zA P D * zbiA P D), hcan, mul_smul_comm, smul_mul_assoc, mul_add]`. Use `congr 2`. Rewrite using `[hcx, mul_assoc, ← mul_assoc (ggA P D), hgi, one_mul]`.
-/
theorem startOK_of (hS : StartIsStart) (hT : T21Commute) (hSc : SSScalar) (hSh : SSShift) (hRho : RhoUp) :
    StartOK := by
  intro P D _ hP l L hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩ := hL
  have hzf : ∀ g ∈ zfns L, ∃ w, g = sc P D w := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨D.zP, hz⟩
    · exact ⟨D.ziP, hzi⟩
    · exact ⟨D.zbP, hzb⟩
    · exact ⟨D.zbiP, hzbi⟩
    · exact ⟨D.ggP P.TT, hgg⟩
    · exact ⟨D.ggiP P.TT, hggi⟩
  refine ⟨hS P D hP l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Y'
    show Commute (sgn P l • t21 P D Y) (sgn P l • t21 P D Y')
    exact ((hT P D hP Y Y').smul_left _).smul_right _
  · intro Y hY
    have hne : ∀ π, x0 P l π Y ≠ 0 := fun π =>
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (hY π)
    have h1 : ((fun π => x0 P l π Y) * fun π => (x0 P l π Y)⁻¹) = (1 : Ty P → ℂ) := by
      funext π; exact mul_inv_cancel₀ (hne π)
    have h2 : ((fun π => (x0 P l π Y)⁻¹) * fun π => x0 P l π Y) = (1 : Ty P → ℂ) := by
      funext π; exact inv_mul_cancel₀ (hne π)
    refine ⟨?_, ?_⟩
    · show (kap P D fun π => x0 P l π Y) * (kap P D fun π => (x0 P l π Y)⁻¹) = 1
      rw [← map_mul, h1, map_one]
    · show (kap P D fun π => (x0 P l π Y)⁻¹) * (kap P D fun π => x0 P l π Y) = 1
      rw [← map_mul, h2, map_one]
  · intro Y Y'
    exact kap_comm_kap P D _ _
  · intro Y g hg
    obtain ⟨w, rfl⟩ := hzf g hg
    exact kap_comm_sc P D _ w
  · intro Y
    rw [hnab]
    exact kap_comm_diag P D _ _
  · intro Y hY
    show star (kap P D fun π => x0 P l π Y) = kap P D fun π => x0 P l π Y
    rw [star_kap]
    congr 1
    funext π
    exact coordinate_real P D l π Y hY
  · intro Y g hg
    have h1 : Commute (zA P D) g := by
      rw [← hz]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h2 : Commute (zbiA P D) g := by
      rw [← hzbi]; exact L.fns_comm _ (Or.inr (by simp)) g (Or.inr hg)
    have h3 : Commute (∑ j ∈ Icc 1 (P.k - 1), (kap P D fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P D j) g := by
      obtain ⟨w, hw⟩ := hzf g hg
      rw [hw]
      exact Commute.sum_left _ _ _ fun j _ => (kap_comm_sc P D _ w).mul_left (hSc P D j w)
    exact (h1.mul_left h2).mul_left h3
  · intro Y
    show sgn P l • (ggA P D * xA P D Y) = L.GG * kap P D (fun π => x0 P l π Y)
    rw [kappa_sign_coordinate, mul_smul_comm, hgg]
  · intro Y hY
    have hl0 : L.l0 Y = l0A P D Y := by simp only [LevelData.l0, l0A, hnab, hzb, hggi]
    have hcan := fn_cancel L
    have hgi := L.GG_GGi
    rw [hzb, hzi, hggi, hz, hzbi] at hcan
    rw [hgg, hggi] at hgi
    have hcx : ggA P D * xA P D Y = xA P D Y * ggA P D := (kap_comm_sc P D _ _).eq.symm
    show sgn P l • (ggA P D * xA P D Y * l0A P D Y + weightedSumBis P D Y) =
      L.GG * (kap P D fun π => x0 P l π Y) * (L.l0 Y + L.ζb * L.ζi * L.GGi * eeA P D Y)
    rw [hl0, kappa_sign_coordinate, hgg, hzb, hzi, hggi, ← low_sum hSh hRho P D Y hY, eeA, ← mul_assoc _ (zA P D * zbiA P D), hcan,
      mul_smul_comm, smul_mul_assoc, mul_add]
    congr 2
    rw [hcx, mul_assoc, ← mul_assoc (ggA P D), hgi, one_mul]

/- English proof (translation)
Introduce `x hx`. Take `⟨hs, -⟩` from `starGens P D`. Take `⟨h1, h2, h3⟩` from `hs i`. Break down `(hx : x ∈ hol (siteA P D i) ∨ star x ∈ hol (siteA P D i)) with hx | hx` into its components or cases. Simplify using `only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`.

Apply the tactic sequence `rcases hx with rfl | rfl | rfl <;> simp`. Simplify using `only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx`. Establish `e : x = star (star x)` using `(star_star x).symm`. Apply the tactic sequence `rcases hx with hx | hx | hx <;> rw [e, hx] <;> simp [h1, h2, h3]`.
-/
theorem ops_sub (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) : ∀ x ∈ ops (siteA P D i),
    x ∈ ({pA P D i, cA P D i, ciA P D i, -pbA P D i, cbA P D i, cbiA P D i} : Set (A P D)) := by
  intro x hx
  obtain ⟨hs, -⟩ := starGens P D
  obtain ⟨h1, h2, h3⟩ := hs i
  rcases (hx : x ∈ hol (siteA P D i) ∨ star x ∈ hol (siteA P D i)) with hx | hx
  · simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;> simp
  · simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have e : x = star (star x) := (star_star x).symm
    rcases hx with hx | hx | hx <;> rw [e, hx] <;> simp [h1, h2, h3]

/- English proof (translation)
Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Introduce `x hx`. Use `ops_sub P D i x hx` as an intermediate fact. Simplify `this` using `only [G, hp, hpb, hc, hci, hcb, hcbi]`.
-/
theorem ops_G (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (L : LevelData (A P D) P.r) (hL : IsModelLevel P D L) (i : Fin P.r) :
    ∀ x ∈ ops (siteA P D i), x ∈ G L i := by
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  intro x hx
  have := ops_sub P D i x hx
  simpa only [G, hp, hpb, hc, hci, hcb, hcbi] using this

/- English proof (translation)
Introduce `x hx`. Use `ops_sub P D i x hx` as an intermediate fact. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at this`. Break down `this with rfl | rfl | rfl | rfl | rfl | rfl` into its components or cases. Conclude with `⟨D.pP i, rfl⟩`.

Conclude with `⟨D.cP i, rfl⟩`. Conclude with `⟨D.ciP i, rfl⟩`. Use `⟨-D.pbP i, ?_⟩` and prove the remaining obligations. Unfold `pbA sc`. Rewrite using `[map_neg]`.

Conclude with `⟨D.cbP i, rfl⟩`. Conclude with `⟨D.cbiP i, rfl⟩`.
-/
theorem ops_sc (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) : ∀ x ∈ ops (siteA P D i), ∃ w, x = sc P D w := by
  intro x hx
  have := ops_sub P D i x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨D.pP i, rfl⟩
  · exact ⟨D.cP i, rfl⟩
  · exact ⟨D.ciP i, rfl⟩
  · refine ⟨-D.pbP i, ?_⟩
    unfold pbA sc
    rw [map_neg]
  · exact ⟨D.cbP i, rfl⟩
  · exact ⟨D.cbiP i, rfl⟩

/- English proof (translation)
Introduce `x hx`. Break down `(hx : x ∈ hol σ ∨ star x ∈ hol σ) with hx | hx` into its components or cases. Conclude with `Or.inr (by rw [star_star]; exact hx)`. Conclude with `Or.inl hx`.
-/
theorem star_ops {A : Type} [Ring A] [StarRing A] (σ : Site A) : ∀ x ∈ ops σ, star x ∈ ops σ := by
  intro x hx
  rcases (hx : x ∈ hol σ ∨ star x ∈ hol σ) with hx | hx
  · exact Or.inr (by rw [star_star]; exact hx)
  · exact Or.inl hx

/- English proof (translation)
Take `⟨L, hL⟩` from `levelExists P D`. Take `⟨hs, -⟩` from `starGens P D`. Take `⟨h1, h2, h3⟩` from `hs i`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, -⟩` from `hL`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `L.c_ci i` as an intermediate fact. Rewrite `this` using `[hc, hci]`. Then use the resulting hypothesis. Use `L.ci_c i` as an intermediate fact. Rewrite `this` using `[hc, hci]`. Then use the resulting hypothesis. Use `L.p_c i i` as an intermediate fact.

Rewrite `this` using `[if_pos rfl, hp, hc]`. Then use the resulting hypothesis. Establish `key` using `hol_comm L i`. Rewrite `key` using `[hp, hpb, hc, hci, hcb, hcbi]`. Introduce `x hx y hy`. Use `key x hx (star y) ?_` and prove the remaining obligations.

Simplify using `only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hy`. Apply the tactic sequence `rcases hy with rfl | rfl | rfl <;> simp [h1, h2, h3]`.
-/
theorem isSiteA (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) : IsSite (siteA P D i) := by
  obtain ⟨L, hL⟩ := levelExists P D
  obtain ⟨hs, -⟩ := starGens P D
  obtain ⟨h1, h2, h3⟩ := hs i
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · have := L.c_ci i; rwa [hc, hci] at this
  · have := L.ci_c i; rwa [hc, hci] at this
  · have := L.p_c i i; rwa [if_pos rfl, hp, hc] at this
  · have key := hol_comm L i
    rw [hp, hpb, hc, hci, hcb, hcbi] at key
    intro x hx y hy
    refine key x hx (star y) ?_
    simp only [hol, siteA, Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> simp [h1, h2, h3]

/- English proof (translation)
Take `⟨L, hL⟩` from `levelExists P D`. Conclude with `fun x hx y hy => G_comm_ne L i j h x (ops_G P D L hL i x hx) y (ops_G P D L hL j y hy)`.
-/
theorem sitesCommuteA (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i j : Fin P.r) (h : i ≠ j) : SitesCommute (siteA P D i) (siteA P D j) := by
  obtain ⟨L, hL⟩ := levelExists P D
  exact fun x hx y hy => G_comm_ne L i j h x (ops_G P D L hL i x hx) y (ops_G P D L hL j y hy)

noncomputable def Cen (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) : Subalgebra ℂ (A P D) := Subalgebra.centralizer ℂ (ops (siteA P D i))

/- English proof (translation)
The claim follows from `Subalgebra.mem_centralizer_iff ℂ`.
-/
theorem mem_Cen {P : Par} {D : DAlg P.r} [Fact (D.Laws P.TT)] {i : Fin P.r} {z : A P D} :
    z ∈ Cen P D i ↔ ∀ g ∈ ops (siteA P D i), Commute g z := Subalgebra.mem_centralizer_iff ℂ

/- English proof (translation)
Rewrite `h`, the goal using `[mem_Cen]`. Introduce `g hg`. Use `(h (star g) (star_ops _ g hg)).star_star` as an intermediate fact. Rewrite `this` using `[star_star]`. Then use the resulting hypothesis.
-/
theorem star_mem_Cen {P : Par} {D : DAlg P.r} [Fact (D.Laws P.TT)] {i : Fin P.r} {z : A P D} (h : z ∈ Cen P D i) : star z ∈ Cen P D i := by
  rw [mem_Cen] at h ⊢
  intro g hg
  have := (h (star g) (star_ops _ g hg)).star_star
  rwa [star_star] at this

/- English proof (translation)
Rewrite using `[mem_Cen]`. Introduce `g hg`. Take `⟨w, rfl⟩` from `ops_sc P D i g hg`. Conclude with `(kap_comm_sc P D f w).symm`.
-/
theorem kap_mem (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) (f : Ty P → ℂ) : kap P D f ∈ Cen P D i := by
  rw [mem_Cen]
  intro g hg
  obtain ⟨w, rfl⟩ := ops_sc P D i g hg
  exact (kap_comm_sc P D f w).symm

/- English proof (translation)
Rewrite using `[mem_Cen]`. Introduce `g hg`. Take `⟨w, rfl⟩` from `ops_sc P D i g hg`. Conclude with `(ssScalar P D l w).symm`.
-/
theorem SS_mem (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) (l : ℕ) : SS P D l ∈ Cen P D i := by
  rw [mem_Cen]
  intro g hg
  obtain ⟨w, rfl⟩ := ops_sc P D i g hg
  exact (ssScalar P D l w).symm

/- English proof (translation)
Take `⟨L, hL⟩` from `levelExists P D`. Establish `key` using `gamma_family_commute_generators L i`. Establish `hG` using `ops_G P D L hL i`. Take `⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩` from `hL`. Rewrite `key` using `[hz, hzb, hgg, hggi, hnab, hnabs]`.

Introduce `y hy`. Rewrite using `[mem_Cen]`. Conclude with `fun g hg => key g (hG g hg) y hy`.
-/
theorem z_mem (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) : ∀ y ∈ ({zA P D, zbA P D, ggA P D, ggiA P D, nabA P D, nabsA P D} : Set (A P D)),
    y ∈ Cen P D i := by
  obtain ⟨L, hL⟩ := levelExists P D
  have key := gamma_family_commute_generators L i
  have hG := ops_G P D L hL i
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, hgg, hggi, hnab, hnabs, hTT⟩ := hL
  rw [hz, hzb, hgg, hggi, hnab, hnabs] at key
  intro y hy
  rw [mem_Cen]
  exact fun g hg => key g (hG g hg) y hy

def Ent {A : Type} [Ring A] [Algebra ℂ A] (C : Subalgebra ℂ A) (M : M2 A) : Prop := ∀ a b, M a b ∈ C

section Ent

variable {A : Type} [Ring A] [Algebra ℂ A] {C : Subalgebra ℂ A}

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Conclude with `sum_mem fun c _ => mul_mem (hM a c) (hN c b)`.
-/
theorem Ent.mul {M N : M2 A} (hM : Ent C M) (hN : Ent C N) : Ent C (M * N) := by
  intro a b
  rw [Matrix.mul_apply]
  exact sum_mem fun c _ => mul_mem (hM a c) (hN c b)

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem C`. Conclude with `zero_mem C`.
-/
theorem Ent.one : Ent C (1 : M2 A) := by
  intro a b
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem C
  · exact zero_mem C

/- English proof (translation)
The claim follows from `List.prod_induction (Ent C) (fun _ _ => Ent.mul) Ent.one h`.
-/
theorem Ent.prod {l : List (M2 A)} (h : ∀ M ∈ l, Ent C M) : Ent C l.prod :=
  List.prod_induction (Ent C) (fun _ _ => Ent.mul) Ent.one h

/- English proof (translation)
Introduce `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show algebraMap ℂ A Y + σ.p ∈ C`. Conclude with `add_mem (C.algebraMap_mem Y) hp`. Use `show -σ.c ∈ C`.

Conclude with `neg_mem hc`. Conclude with `hci`. Conclude with `zero_mem C`.
-/
theorem Ent.Ts {σ : Site A} (hp : σ.p ∈ C) (hc : σ.c ∈ C) (hci : σ.ci ∈ C) (Y : ℂ) : Ent C (Ts σ Y) := by
  intro a b
  fin_cases a <;> fin_cases b
  · show algebraMap ℂ A Y + σ.p ∈ C
    exact add_mem (C.algebraMap_mem Y) hp
  · show -σ.c ∈ C
    exact neg_mem hc
  · exact hci
  · exact zero_mem C

end Ent

/- English proof (translation)
Establish `hz : zA P D ∈ Cen P D i` using `z_mem P D i _ (by simp)`. Establish `hzb : zbA P D ∈ Cen P D i` using `z_mem P D i _ (by simp)`. Establish `hgg : ggA P D ∈ Cen P D i` using `z_mem P D i _ (by simp)`. Establish `hggi : ggiA P D ∈ Cen P D i` using `z_mem P D i _ (by simp)`. Establish `hnab : nabA P D ∈ Cen P D i` using `z_mem P D i _ (by simp)`.

Establish `hnabs : nabsA P D ∈ Cen P D i` using `z_mem P D i _ (by simp)`. Establish `hk` using `kap_mem P D i`. Establish `hS` using `SS_mem P D i`. Establish `hSs : ∀ l, star (SS P D l) ∈ Cen P D i` using `fun l => star_mem_Cen (hS l)`. Establish `hl0 : l0A P D Y ∈ Cen P D i` using `sub_mem (neg_mem hnab) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hggi))`.

Establish `hm0 : m0A P D Y ∈ Cen P D i` using `sub_mem (neg_mem hnabs) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hggi))`. Establish `hx : xA P D Y ∈ Cen P D i` using `hk _`. Establish `h21 : weightedSumBis P D Y ∈ Cen P D i` using `sum_mem fun l _ => mul_mem (hS l) (hk _)`. Establish `h12 : S12 P D Y ∈ Cen P D i` using `sum_mem fun l _ => mul_mem (hk _) (hSs l)`. Establish `h4 : S4 P D Y ∈ Cen P D i` using `sum_mem fun l _ => sum_mem fun j _ => mul_mem (mul_mem (hSs l) (hS j)) (hk _)`.

Introduce `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b`. Use `show t11 P D Y ∈ Cen P D i`. Conclude with `add_mem (add_mem (add_mem (add_mem (mul_mem hggi (hk _)) (mul_mem (mul_mem (mul_mem hgg hx) hm0) hl0)) (mul_mem (mul_mem (mul_mem hgg hm0) hggi) h21)) (mul_mem h12 hl0)) (mul_mem hggi h4)`. Use `show t12 P D Y ∈ Cen P D i`.

Conclude with `add_mem (mul_mem (mul_mem hgg hx) hm0) h12`. Use `show t21 P D Y ∈ Cen P D i`. Conclude with `add_mem (mul_mem (mul_mem hgg hx) hl0) h21`. Use `show t22 P D Y ∈ Cen P D i`. Conclude with `mul_mem hgg hx`.
-/
theorem QQr_ent (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) (Y : ℂ) : Ent (Cen P D i) (QQr P D Y) := by
  have hz : zA P D ∈ Cen P D i := z_mem P D i _ (by simp)
  have hzb : zbA P D ∈ Cen P D i := z_mem P D i _ (by simp)
  have hgg : ggA P D ∈ Cen P D i := z_mem P D i _ (by simp)
  have hggi : ggiA P D ∈ Cen P D i := z_mem P D i _ (by simp)
  have hnab : nabA P D ∈ Cen P D i := z_mem P D i _ (by simp)
  have hnabs : nabsA P D ∈ Cen P D i := z_mem P D i _ (by simp)
  have hk := kap_mem P D i
  have hS := SS_mem P D i
  have hSs : ∀ l, star (SS P D l) ∈ Cen P D i := fun l => star_mem_Cen (hS l)
  have hl0 : l0A P D Y ∈ Cen P D i :=
    sub_mem (neg_mem hnab) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hzb hggi))
  have hm0 : m0A P D Y ∈ Cen P D i :=
    sub_mem (neg_mem hnabs) (mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem hz hggi))
  have hx : xA P D Y ∈ Cen P D i := hk _
  have h21 : weightedSumBis P D Y ∈ Cen P D i := sum_mem fun l _ => mul_mem (hS l) (hk _)
  have h12 : S12 P D Y ∈ Cen P D i := sum_mem fun l _ => mul_mem (hk _) (hSs l)
  have h4 : S4 P D Y ∈ Cen P D i :=
    sum_mem fun l _ => sum_mem fun j _ => mul_mem (mul_mem (hSs l) (hS j)) (hk _)
  intro a b
  fin_cases a <;> fin_cases b
  · show t11 P D Y ∈ Cen P D i
    exact add_mem (add_mem (add_mem (add_mem (mul_mem hggi (hk _))
      (mul_mem (mul_mem (mul_mem hgg hx) hm0) hl0)) (mul_mem (mul_mem (mul_mem hgg hm0) hggi) h21))
      (mul_mem h12 hl0)) (mul_mem hggi h4)
  · show t12 P D Y ∈ Cen P D i
    exact add_mem (mul_mem (mul_mem hgg hx) hm0) h12
  · show t21 P D Y ∈ Cen P D i
    exact add_mem (mul_mem (mul_mem hgg hx) hl0) h21
  · show t22 P D Y ∈ Cen P D i
    exact mul_mem hgg hx

/- English proof (translation)
Introduce `a b` and use `(Cen P D i).smul_mem (QQr_ent P D i Y a b) (sgn P l)`.
-/
theorem start_ent (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (i : Fin P.r) (Y : ℂ) : Ent (Cen P D i) ((startM P D l).QQ Y) :=
  fun a b => (Cen P D i).smul_mem (QQr_ent P D i Y a b) (sgn P l)

/- English proof (translation)
Introduce `Y a b x hx` and use `(mem_Cen.1 (h Y a b) x hx).symm`.
-/
theorem commutes_of_ent (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) (QQ : ℂ → M2 (A P D)) (h : ∀ Y, Ent (Cen P D i) (QQ Y)) :
    QQCommutes QQ (siteA P D i) :=
  fun Y a b x hx => (mem_Cen.1 (h Y a b) x hx).symm

/- English proof (translation)
Establish `key : ∀ y ∈ hol (siteA P D j), y ∈ Cen P D i` using `fun y hy => mem_Cen.2 fun g hg => sitesCommuteA P D i j h g hg y (Or.inl hy)`. Conclude with `Ent.Ts (key _ (by simp [hol])) (key _ (by simp [hol])) (key _ (by simp [hol])) Y`.
-/
theorem Ts_ent (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i j : Fin P.r) (h : i ≠ j) (Y : ℂ) : Ent (Cen P D i) (Ts (siteA P D j) Y) := by
  have key : ∀ y ∈ hol (siteA P D j), y ∈ Cen P D i := fun y hy =>
    mem_Cen.2 fun g hg => sitesCommuteA P D i j h g hg y (Or.inl hy)
  exact Ent.Ts (key _ (by simp [hol])) (key _ (by simp [hol])) (key _ (by simp [hol])) Y

/- English proof (translation)
Unfold `sitesFromD at h`. Rewrite `h` using `[List.mem_reverse]`. Take `⟨k, hk, rfl⟩` from `List.mem_iff_getElem.1 h`. Rewrite `hk` using `[List.length_drop, List.length_ofFn]`. Use `⟨⟨n + k, by omega⟩, Nat.le_add_right _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[List.getElem_drop, List.getElem_ofFn]`.
-/
theorem mem_sitesFrom (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (n : ℕ) (σ : Site (A P D)) (h : σ ∈ sitesFromD P D n) :
    ∃ j : Fin P.r, n ≤ j ∧ σ = siteA P D j := by
  unfold sitesFromD at h
  rw [List.mem_reverse] at h
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 h
  rw [List.length_drop, List.length_ofFn] at hk
  refine ⟨⟨n + k, by omega⟩, Nat.le_add_right _ _, ?_⟩
  rw [List.getElem_drop, List.getElem_ofFn]

/- English proof (translation)
Establish `hT : ∀ Z : ℂ, Ent (Cen P D i) (((sitesFromD P D (i + 1)).map fun σ => Ts σ Z).prod)`. Introduce `Z`. Use `Ent.prod fun M hM => ?_` and prove the remaining obligations. Take `⟨σ, hσ, rfl⟩` from `List.mem_map.1 hM`. Take `⟨j, hj, rfl⟩` from `mem_sitesFrom P D _ σ hσ`.

Use `Ts_ent P D i j ?_ Z` and prove the remaining obligations. Introduce `e`. Rewrite `hj` using `[e]`. Use linear arithmetic over natural numbers and integers. Use `Ent.mul (Ent.mul ?_ (start_ent P D l i Y)) (hT Y)` and prove the remaining obligations.

Introduce `a b`. Rewrite using `[Matrix.conjTranspose_apply]`. Conclude with `star_mem_Cen (hT (star Y) b a)`.
-/
theorem QQlev_ent (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (l : ℕ) (i : Fin P.r) (Y : ℂ) : Ent (Cen P D i) (QQlev P D l (i + 1) Y) := by
  have hT : ∀ Z : ℂ, Ent (Cen P D i) (((sitesFromD P D (i + 1)).map fun σ => Ts σ Z).prod) := by
    intro Z
    refine Ent.prod fun M hM => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hM
    obtain ⟨j, hj, rfl⟩ := mem_sitesFrom P D _ σ hσ
    refine Ts_ent P D i j ?_ Z
    intro e
    rw [e] at hj
    omega
  refine Ent.mul (Ent.mul ?_ (start_ent P D l i Y)) (hT Y)
  intro a b
  rw [Matrix.conjTranspose_apply]
  exact star_mem_Cen (hT (star Y) b a)

/- English proof (translation)
Unfold `sitesFromD`. Rewrite using `[List.drop_eq_getElem_cons (by simp), List.reverse_cons]`. Simplify using the standard rewrite rules.
-/
theorem sites_step (P : Par) (D : DAlg P.r) [Fact (D.Laws P.TT)] (i : Fin P.r) : sitesFromD P D i = sitesFromD P D (i + 1) ++ [siteA P D i] := by
  unfold sitesFromD
  rw [List.drop_eq_getElem_cons (by simp), List.reverse_cons]
  simp

/- English proof (translation)
Introduce `P D _ l`. Use `⟨fun Y => ?_, fun i Y => ?_⟩` and prove the remaining obligations. Establish `h : sitesFromD P D P.r = []`. Unfold `sitesFromD`. Rewrite using `[List.drop_eq_nil_of_le (by simp)]; rfl`.

Simplify using `[QQlev, h]`. Simplify using `only [QQlev, sites_step P D i, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc]`.
-/
theorem chainM : ChainM := by
  intro P D _ l
  refine ⟨fun Y => ?_, fun i Y => ?_⟩
  · have h : sitesFromD P D P.r = [] := by
      unfold sitesFromD
      rw [List.drop_eq_nil_of_le (by simp)]; rfl
    simp [QQlev, h]
  · simp only [QQlev, sites_step P D i, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/- English proof (translation)
Introduce `P D _ l i` and use `commutes_of_ent P D i _ (QQlev_ent P D l i)`.
-/
theorem lowerCommutes : LowerCommutes :=
  fun P D _ l i => commutes_of_ent P D i _ (QQlev_ent P D l i)

/- English proof (translation)
Introduce `P D _ hP l`. Establish `key : ∀ d i : ℕ, i + d = P.r → IsStart (QQlev P D l i) (qC P)`. Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`.

Introduce `i hi`. Establish `e : QQlev P D l i = (startM P D l).QQ`. Use function extensionality and compare the values at `Y`. Rewrite using `[show i = P.r by omega]`. Conclude with `(chainM P D l).1 Y`.

Rewrite using `[e]`. Conclude with `h P D hP l`. Consider the case `succ d ih`. Introduce `i hi`. Establish `hlt : i < P.r` using `by omega`.

Establish `e : QQlev P D l i = fun Y => (Ts (siteA P D ⟨i, hlt⟩) (star Y))ᴴ * QQlev P D l (i + 1) Y * Ts (siteA P D ⟨i, hlt⟩) Y`. Use function extensionality and compare the values at `Y`. Conclude with `(chainM P D l).2 ⟨i, hlt⟩ Y`. Rewrite using `[e]`. Conclude with `isStart_step _ _ _ (isSiteA P D _) (lowerCommutes P D l ⟨i, hlt⟩) (ih (i + 1) (by omega))`.

Introduce `i hi`. Conclude with `key (P.r - i) i (by omega)`.
-/
theorem lowerStart_of (h : StartIsStart) : LowerStart := by
  intro P D _ hP l
  have key : ∀ d i : ℕ, i + d = P.r → IsStart (QQlev P D l i) (qC P) := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have e : QQlev P D l i = (startM P D l).QQ := by
        funext Y
        rw [show i = P.r by omega]
        exact (chainM P D l).1 Y
      rw [e]
      exact h P D hP l
    | succ d ih =>
      intro i hi
      have hlt : i < P.r := by omega
      have e : QQlev P D l i = fun Y => (Ts (siteA P D ⟨i, hlt⟩) (star Y))ᴴ * QQlev P D l (i + 1) Y *
          Ts (siteA P D ⟨i, hlt⟩) Y := by
        funext Y
        exact (chainM P D l).2 ⟨i, hlt⟩ Y
      rw [e]
      exact isStart_step _ _ _ (isSiteA P D _) (lowerCommutes P D l ⟨i, hlt⟩) (ih (i + 1) (by omega))
  intro i hi
  exact key (P.r - i) i (by omega)

end

end Formalism.FourierDecayAlt.P.MAx1.WeylSymmetry

namespace Formalism.FourierDecayAlt.P.MAx1

open Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.YangianSpanCharacter.T

/- English proof (translation)
Introduce `hH hR hD P D _ hP l`. Conclude with `WeylSymmetry.isStart_smul (QQr P D) (qC P) (sgn P l) (WeylSymmetry.sgn_sq P D l) (WeylSymmetry.sgn_star P D l) ⟨fun Y hY => by rw [hH P D hP Y, hY], hR P D hP, hD P D hP, WeylSymmetry.qC_real P D⟩`.
-/
theorem startIsStartAssemble : StartIsStartAssemble := by
  intro hH hR hD P D _ hP l
  exact WeylSymmetry.isStart_smul (QQr P D) (qC P) (sgn P l) (WeylSymmetry.sgn_sq P D l) (WeylSymmetry.sgn_star P D l)
    ⟨fun Y hY => by rw [hH P D hP Y, hY], hR P D hP, hD P D hP, WeylSymmetry.qC_real P D⟩

/- English proof (translation)
The claim follows from `WeylSymmetry.startOK_of`.
-/
theorem startAssemble : StartAssemble := WeylSymmetry.startOK_of

/- English proof (translation)
Introduce `P D _ l`. Use `⟨fun σ hσ => ?_, ?_⟩` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `WeylSymmetry.mem_sitesFrom P D 0 σ hσ`. Conclude with `⟨WeylSymmetry.isSiteA P D j, WeylSymmetry.commutes_of_ent P D j _ (WeylSymmetry.start_ent P D l j)⟩`. Unfold `sitesFromD`.

Rewrite using `[List.drop_zero, List.pairwise_reverse, List.pairwise_ofFn]`. Introduce `i j hij`. Conclude with `WeylSymmetry.sitesCommuteA P D j i (ne_of_gt hij)`.
-/
theorem sitesOKM : SitesOKM := by
  intro P D _ l
  refine ⟨fun σ hσ => ?_, ?_⟩
  · obtain ⟨j, -, rfl⟩ := WeylSymmetry.mem_sitesFrom P D 0 σ hσ
    exact ⟨WeylSymmetry.isSiteA P D j, WeylSymmetry.commutes_of_ent P D j _ (WeylSymmetry.start_ent P D l j)⟩
  · unfold sitesFromD
    rw [List.drop_zero, List.pairwise_reverse, List.pairwise_ofFn]
    intro i j hij
    exact WeylSymmetry.sitesCommuteA P D j i (ne_of_gt hij)

/- English proof (translation)
The claim follows from `WeylSymmetry.chainM`.
-/
theorem chainM : ChainM := WeylSymmetry.chainM

/- English proof (translation)
The claim follows from `WeylSymmetry.lowerCommutes`.
-/
theorem lowerCommutes : LowerCommutes := WeylSymmetry.lowerCommutes

end Formalism.FourierDecayAlt.P.MAx1

end

section

namespace Formalism.FourierDecayAlt.P.MAx1.An

open Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt
open scoped ComplexConjugate

noncomputable section

variable {r : ℕ} {TT : ℝ}

def sg (v : M.Var r) : ℂ := if (ofLex v).2 = 0 then -Complex.I else Complex.I

/- English proof (translation)
Simplify using `[ext, hx]`.
-/
theorem ext_of_mem (f : Qp r TT → ℂ) {x : E r} (hx : x ∈ Qset r TT) : ext f x = f ⟨x, hx⟩ := by
  simp [ext, hx]

/- English proof (translation)
Apply the tactic sequence `funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]`.
-/
theorem ext_mul (f g : Qp r TT → ℂ) : ext (f * g) = ext f * ext g := by
  funext x; by_cases hx : x ∈ Qset r TT <;> simp [ext, hx]

/- English proof (translation)
Use `filter_upwards [(Qset_open r TT).mem_nhds hx] with y hy`. Simplify using `[ext, hy]`.
-/
theorem ext_comp_ev (F : E r → ℂ) {x : E r} (hx : x ∈ Qset r TT) :
    ext (fun q : Qp r TT => F q.1) =ᶠ[nhds x] F := by
  filter_upwards [(Qset_open r TT).mem_nhds hx] with y hy
  simp [ext, hy]

/- English proof (translation)
Simplify using `only [wirt, h.fderiv_eq]`.
-/
theorem wirt_congr (v : M.Var r) {F G : E r → ℂ} {x : E r} (h : F =ᶠ[nhds x] G) :
    wirt v F x = wirt v G x := by
  simp only [wirt, h.fderiv_eq]

/- English proof (translation)
Rewrite using `[wirt, wirt, wirt, show (fun y => F y * G y) = F * G from rfl, (hF.hasFDerivAt.mul hG.hasFDerivAt).fderiv]`. Simplify using `only [add_apply, smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_mul (v : M.Var r) {F G : E r → ℂ} {x : E r} (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) :
    wirt v (fun y => F y * G y) x = wirt v F x * G x + F x * wirt v G x := by
  rw [wirt, wirt, wirt, show (fun y => F y * G y) = F * G from rfl, (hF.hasFDerivAt.mul hG.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

def zLC (w : M.Var r) : E r →L[ℂ] ℂ :=
  if h : ((ofLex w).1 : ℕ) < r then
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) ⟨_, h⟩).comp (ContinuousLinearMap.fst ℂ _ _)
  else ContinuousLinearMap.snd ℂ _ _

def cL (w : M.Var r) : E r →L[ℝ] ℂ :=
  if (ofLex w).2 = 0 then (zLC w).restrictScalars ℝ
  else (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp ((zLC w).restrictScalars ℝ)

/- English proof (translation)
Unfold `zLC zE`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem zLC_apply (w : M.Var r) (y : E r) : zLC w y = zE w y := by
  unfold zLC zE
  split_ifs <;> simp

/- English proof (translation)
Unfold `cL coordE`. Apply the tactic sequence `split_ifs <;> simp [zLC_apply]`.
-/
theorem cL_apply (w : M.Var r) (y : E r) : cL w y = coordE w y := by
  unfold cL coordE
  split_ifs <;> simp [zLC_apply]

/- English proof (translation)
The claim follows from `funext fun y => (cL_apply w y).symm`.
-/
theorem coordE_eq (w : M.Var r) : coordE w = ⇑(cL w) := funext fun y => (cL_apply w y).symm

/- English proof (translation)
Rewrite using `[coordE_eq]`. Conclude with `(cL w).fderiv`.
-/
theorem fderiv_coordE (w : M.Var r) (x : E r) : fderiv ℝ (coordE w) x = cL w := by
  rw [coordE_eq]; exact (cL w).fderiv

/- English proof (translation)
Rewrite using `[coordE_eq]`. Conclude with `(cL w).differentiableAt`.
-/
theorem coordE_diff (w : M.Var r) (x : E r) : DifferentiableAt ℝ (coordE w) x := by
  rw [coordE_eq]; exact (cL w).differentiableAt

def dl (v w : M.Var r) : ℂ := if ((ofLex v).1 : ℕ) = (ofLex w).1 then 1 else 0

/- English proof (translation)
Unfold `zLC dirE dl`. Establish `hv'` using `(ofLex v).1.isLt`. Establish `hw'` using `(ofLex w).1.isLt`. Apply the tactic sequence `by_cases hw : ((ofLex w).1 : ℕ) < r <;> by_cases hv : ((ofLex v).1 : ℕ) < r`. Simplify using `only [hw, hv, dif_pos, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, Pi.single_apply] split_ifs with h1 h2 h2`.

Both sides reduce to the same expression. Conclude with `absurd (congrArg Fin.val h1).symm h2`. Conclude with `(h1 (Fin.ext h2.symm)).elim`. Both sides reduce to the same expression. Simplify using `only [hw, hv, dif_pos, dif_neg, not_false_eq_true, ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, Pi.zero_apply]`.

Rewrite using `[if_neg (by omega : ¬ (((ofLex v).1 : ℕ) = (ofLex w).1))]`. Simplify using `only [hw, hv, dif_pos, dif_neg, not_false_eq_true, ContinuousLinearMap.coe_snd']`. Rewrite using `[if_neg (by omega : ¬ (((ofLex v).1 : ℕ) = (ofLex w).1))]`. Simplify using `only [hw, hv, dif_neg, not_false_eq_true, ContinuousLinearMap.coe_snd']`. Rewrite using `[if_pos (by omega)]`.
-/
theorem zLC_dir (v w : M.Var r) : zLC w (dirE v) = dl v w := by
  unfold zLC dirE dl
  have hv' := (ofLex v).1.isLt
  have hw' := (ofLex w).1.isLt
  by_cases hw : ((ofLex w).1 : ℕ) < r <;> by_cases hv : ((ofLex v).1 : ℕ) < r
  · simp only [hw, hv, dif_pos, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, Pi.single_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (congrArg Fin.val h1).symm h2
    · exact (h1 (Fin.ext h2.symm)).elim
    · rfl
  · simp only [hw, hv, dif_pos, dif_neg, not_false_eq_true, ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, Pi.zero_apply]
    rw [if_neg (by omega : ¬ (((ofLex v).1 : ℕ) = (ofLex w).1))]
  · simp only [hw, hv, dif_pos, dif_neg, not_false_eq_true, ContinuousLinearMap.coe_snd']
    rw [if_neg (by omega : ¬ (((ofLex v).1 : ℕ) = (ofLex w).1))]
  · simp only [hw, hv, dif_neg, not_false_eq_true, ContinuousLinearMap.coe_snd']
    rw [if_pos (by omega)]

/- English proof (translation)
Apply the tactic sequence `unfold dl; split_ifs <;> simp`.
-/
theorem conj_dl (v w : M.Var r) : conj (dl v w) = dl v w := by
  unfold dl; split_ifs <;> simp

/- English proof (translation)
Unfold `cL`. Use `split_ifs`. Rewrite using `[ContinuousLinearMap.coe_restrictScalars', zLC_dir]`. Simplify using `only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, zLC_dir, conj_dl]`.
-/
theorem cL_dir (v w : M.Var r) : cL w (dirE v) = dl v w := by
  unfold cL
  split_ifs
  · rw [ContinuousLinearMap.coe_restrictScalars', zLC_dir]
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, zLC_dir, conj_dl]

/- English proof (translation)
Establish `hs : zLC w (Complex.I • dirE v) = Complex.I * zLC w (dirE v)` using `by rw [map_smul, smul_eq_mul]`. Unfold `cL`. Use `split_ifs`. Rewrite using `[ContinuousLinearMap.coe_restrictScalars', hs, zLC_dir]`. Simplify using `only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hs, zLC_dir, map_mul, conj_dl, Complex.conj_I]`.
-/
theorem cL_Idir (v w : M.Var r) :
    cL w (Complex.I • dirE v) = (if (ofLex w).2 = 0 then Complex.I else -Complex.I) * dl v w := by
  have hs : zLC w (Complex.I • dirE v) = Complex.I * zLC w (dirE v) := by rw [map_smul, smul_eq_mul]
  unfold cL
  split_ifs
  · rw [ContinuousLinearMap.coe_restrictScalars', hs, zLC_dir]
  · simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, hs, zLC_dir, map_mul, conj_dl, Complex.conj_I]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨rfl, rfl⟩`. Introduce and unpack `⟨h1, h2⟩`. Establish `: ofLex v = ofLex w` using `Prod.ext (Fin.ext h1) h2`.

Simplify using `using congrArg toLex this`.
-/
theorem var_eq_iff (v w : M.Var r) :
    v = w ↔ ((ofLex v).1 : ℕ) = (ofLex w).1 ∧ (ofLex v).2 = (ofLex w).2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    have : ofLex v = ofLex w := Prod.ext (Fin.ext h1) h2
    simpa using congrArg toLex this

/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
theorem fin2 (a b : Fin 2) (ha : a ≠ 0) (hb : b ≠ 0) : a = b := by omega

/- English proof (translation)
Rewrite using `[wirt, fderiv_coordE, cL_dir, cL_Idir]`. Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`.

Establish `: dl v v = 1` using `by unfold dl; rw [if_pos rfl]`. Rewrite using `[this]`. Distinguish the cases in `ha : (ofLex v).2 = 0`. Simplify using `only [ha, if_true]`. Take the linear combination `(-1 / 2 : ℂ) * hI`.

Simplify using `only [ha, if_false]`. Take the linear combination `(-1 / 2 : ℂ) * hI`. Rewrite using `[if_neg h]`. Distinguish the cases in `h1 : ((ofLex v).1 : ℕ) = (ofLex w).1`. Establish `hd : dl v w = 1` using `by unfold dl; rw [if_pos h1]`.

Rewrite using `[hd]`. Apply the tactic sequence `by_cases ha : (ofLex v).2 = 0 <;> by_cases hb : (ofLex w).2 = 0`. Conclude with `absurd ((var_eq_iff v w).2 ⟨h1, by rw [ha, hb]⟩) h`. Simplify using `only [ha, hb, if_true, if_false]`. Take the linear combination `(1 / 2 : ℂ) * hI`.

Simplify using `only [ha, hb, if_true, if_false]`. Take the linear combination `(1 / 2 : ℂ) * hI`. Conclude with `absurd ((var_eq_iff v w).2 ⟨h1, fin2 _ _ ha hb⟩) h`. Establish `hd : dl v w = 0` using `by unfold dl; rw [if_neg h1]`. Rewrite using `[hd]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_coord (v w : M.Var r) (x : E r) : wirt v (coordE w) x = if v = w then 1 else 0 := by
  rw [wirt, fderiv_coordE, cL_dir, cL_Idir]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  by_cases h : v = w
  · subst h
    rw [if_pos rfl]
    have : dl v v = 1 := by unfold dl; rw [if_pos rfl]
    rw [this]
    by_cases ha : (ofLex v).2 = 0
    · simp only [ha, if_true]; linear_combination (-1 / 2 : ℂ) * hI
    · simp only [ha, if_false]; linear_combination (-1 / 2 : ℂ) * hI
  · rw [if_neg h]
    by_cases h1 : ((ofLex v).1 : ℕ) = (ofLex w).1
    · have hd : dl v w = 1 := by unfold dl; rw [if_pos h1]
      rw [hd]
      by_cases ha : (ofLex v).2 = 0 <;> by_cases hb : (ofLex w).2 = 0
      · exact absurd ((var_eq_iff v w).2 ⟨h1, by rw [ha, hb]⟩) h
      · simp only [ha, hb, if_true, if_false]; linear_combination (1 / 2 : ℂ) * hI
      · simp only [ha, hb, if_true, if_false]; linear_combination (1 / 2 : ℂ) * hI
      · exact absurd ((var_eq_iff v w).2 ⟨h1, fin2 _ _ ha hb⟩) h
    · have hd : dl v w = 0 := by unfold dl; rw [if_neg h1]
      rw [hd]; ring

def WL (w : M.Var r) : (E r →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (dirE w) + sg w • ContinuousLinearMap.apply ℝ ℂ (Complex.I • dirE w))

/- English proof (translation)
Simplify using `[WL, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem WL_apply (w : M.Var r) (L : E r →L[ℝ] ℂ) :
    WL w L = (1 / 2 : ℂ) * (L (dirE w) + sg w * L (Complex.I • dirE w)) := by
  simp [WL, smul_eq_mul]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Rewrite using `[WL_apply]`. Both sides reduce to the same expression.
-/
theorem wirt_eq (w : M.Var r) (F : E r → ℂ) : wirt w F = fun y => WL w (fderiv ℝ F y) := by
  funext y; rw [WL_apply]; rfl

/- English proof (translation)
The claim follows from `WithTop.coe_le_coe.2 le_top`.
-/
theorem le_sm' (n : ℕ∞) : (n : WithTop ℕ∞) ≤ sm := WithTop.coe_le_coe.2 le_top

/- English proof (translation)
Establish `hFx : ContDiffAt ℝ sm F x` using `hF.contDiffAt (hs.mem_nhds hx)`. Establish `hsym : IsSymmSndFDerivAt ℝ F x` using `hFx.isSymmSndFDerivAt (by simpa using le_sm' 2)`. Establish `hd : DifferentiableAt ℝ (fderiv ℝ F) x` using `(hFx.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; simpa using le_sm' 2)).differentiableAt one_ne_zero`. Establish `key : ∀ u : M.Var r, fderiv ℝ (wirt u F) x = (WL u).comp (fderiv ℝ (fderiv ℝ F) x)`. Introduce `u`.

Rewrite using `[wirt_eq]`. Conclude with `((WL u).hasFDerivAt.comp x hd.hasFDerivAt).fderiv`. Establish `e1 : wirt v (wirt w F) x = WL v (fderiv ℝ (wirt w F) x)` using `by rw [wirt_eq v (wirt w F)]`. Establish `e2 : wirt w (wirt v F) x = WL w (fderiv ℝ (wirt v F) x)` using `by rw [wirt_eq w (wirt v F)]`. Rewrite using `[e1, e2, key, key]`.

Simplify using `only [WL_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]`. Rewrite using `[hsym (dirE w) (dirE v), hsym (dirE w) (Complex.I • dirE v), hsym (Complex.I • dirE w) (dirE v), hsym (Complex.I • dirE w) (Complex.I • dirE v)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wirt_wirt (v w : M.Var r) {F : E r → ℂ} {s : Set (E r)} (hs : IsOpen s) (hF : ContDiffOn ℝ sm F s)
    {x : E r} (hx : x ∈ s) : wirt v (wirt w F) x = wirt w (wirt v F) x := by
  have hFx : ContDiffAt ℝ sm F x := hF.contDiffAt (hs.mem_nhds hx)
  have hsym : IsSymmSndFDerivAt ℝ F x := hFx.isSymmSndFDerivAt (by simpa using le_sm' 2)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hFx.fderiv_right (m := 1) (by rw [one_add_one_eq_two]; simpa using le_sm' 2)).differentiableAt one_ne_zero
  have key : ∀ u : M.Var r, fderiv ℝ (wirt u F) x = (WL u).comp (fderiv ℝ (fderiv ℝ F) x) := by
    intro u
    rw [wirt_eq]
    exact ((WL u).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  have e1 : wirt v (wirt w F) x = WL v (fderiv ℝ (wirt w F) x) := by rw [wirt_eq v (wirt w F)]
  have e2 : wirt w (wirt v F) x = WL w (fderiv ℝ (wirt v F) x) := by rw [wirt_eq w (wirt v F)]
  rw [e1, e2, key, key]
  simp only [WL_apply, ContinuousLinearMap.coe_comp, Function.comp_apply, map_add, map_smul,
    add_apply, smul_apply, smul_eq_mul]
  rw [hsym (dirE w) (dirE v), hsym (dirE w) (Complex.I • dirE v), hsym (Complex.I • dirE w) (dirE v),
    hsym (Complex.I • dirE w) (Complex.I • dirE v)]
  ring

/- English proof (translation)
The claim follows from `((wirt_smooth hf v).differentiableOn (by simp [sm]) x hx).differentiableAt ((Qset_open r TT).mem_nhds hx)`.
-/
theorem wirt_diff {f : Qp r TT → ℂ} (hf : f ∈ smSub r TT) (v : M.Var r) {x : E r} (hx : x ∈ Qset r TT) :
    DifferentiableAt ℝ (wirt v (ext f)) x :=
  ((wirt_smooth hf v).differentiableOn (by simp [sm]) x hx).differentiableAt ((Qset_open r TT).mem_nhds hx)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eulerQ_apply (v : M.Var r) (f : SmQ r TT) (q : Qp r TT) :
    ((eulerQ v f : SmQ r TT) : Qp r TT → ℂ) q = coordE v q.1 * wirt v (ext (f : Qp r TT → ℂ)) q.1 := rfl

/- English proof (translation)
Rewrite using `[eulerQ_apply]`. Establish `h1 : ext ((eulerQ w f : SmQ r TT) : Qp r TT → ℂ) =ᶠ[nhds q.1] fun y => coordE w y * wirt w (ext (f : Qp r TT → ℂ)) y` using `ext_comp_ev (fun y => coordE w y * wirt w (ext (f : Qp r TT → ℂ)) y) q.2`. Rewrite using `[wirt_congr v h1, wirt_mul v (coordE_diff w q.1) (wirt_diff f.2 w q.2), wirt_coord]`.
-/
theorem euler_euler (v w : M.Var r) (f : SmQ r TT) (q : Qp r TT) :
    ((eulerQ v (eulerQ w f) : SmQ r TT) : Qp r TT → ℂ) q =
      coordE v q.1 * ((if v = w then 1 else 0) * wirt w (ext (f : Qp r TT → ℂ)) q.1 +
        coordE w q.1 * wirt v (wirt w (ext (f : Qp r TT → ℂ))) q.1) := by
  rw [eulerQ_apply]
  have h1 : ext ((eulerQ w f : SmQ r TT) : Qp r TT → ℂ) =ᶠ[nhds q.1]
      fun y => coordE w y * wirt w (ext (f : Qp r TT → ℂ)) y :=
    ext_comp_ev (fun y => coordE w y * wirt w (ext (f : Qp r TT → ℂ)) y) q.2
  rw [wirt_congr v h1, wirt_mul v (coordE_diff w q.1) (wirt_diff f.2 w q.2), wirt_coord]

/- English proof (translation)
Establish `hs : ContDiffOn ℝ sm (fun x => (ext (f : Qp r TT → ℂ) x)⁻¹) (Qset r TT)` using `(f.2 : ContDiffOn ℝ sm (ext (f : Qp r TT → ℂ)) (Qset r TT)).inv fun x hx => by`. Rewrite using `[ext_of_mem _ hx]`. Conclude with `h _`. Set `g : SmQ r TT` to `⟨fun q => ((f : Qp r TT → ℂ) q)⁻¹, hs.congr fun x hx => by simp [ext, hx]⟩`. Establish `h1 : f * g = 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Use `show (f : Qp r TT → ℂ) q * ((f : Qp r TT → ℂ) q)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ (h q)`. Conclude with `⟨⟨f, g, h1, by rw [mul_comm]; exact h1⟩, rfl⟩`.
-/
theorem isUnit_of_ne (f : SmQ r TT) (h : ∀ q, (f : Qp r TT → ℂ) q ≠ 0) : IsUnit f := by
  have hs : ContDiffOn ℝ sm (fun x => (ext (f : Qp r TT → ℂ) x)⁻¹) (Qset r TT) :=
    (f.2 : ContDiffOn ℝ sm (ext (f : Qp r TT → ℂ)) (Qset r TT)).inv fun x hx => by
      rw [ext_of_mem _ hx]; exact h _
  let g : SmQ r TT := ⟨fun q => ((f : Qp r TT → ℂ) q)⁻¹, hs.congr fun x hx => by simp [ext, hx]⟩
  have h1 : f * g = 1 := by
    apply Subtype.ext; funext q
    show (f : Qp r TT → ℂ) q * ((f : Qp r TT → ℂ) q)⁻¹ = 1
    exact mul_inv_cancel₀ (h q)
  exact ⟨⟨f, g, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

/- English proof (translation)
Establish `hz : zE v x ≠ 0`. Unfold `zE`. Use `split_ifs with h`. Conclude with `hx.1 _`. Introduce `h0`.

Establish `h2 : TT < Complex.normSq x.2` using `hx.2`. Rewrite `h2` using `[h0, Complex.normSq_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `coordE`. Use `split_ifs`.

Conclude with `hz`. Simplify using `using hz`.
-/
theorem coordE_ne {x : E r} (hx : x ∈ Qset r TT) (hTT : 0 ≤ TT) (v : M.Var r) : coordE v x ≠ 0 := by
  have hz : zE v x ≠ 0 := by
    unfold zE
    split_ifs with h
    · exact hx.1 _
    · intro h0
      have h2 : TT < Complex.normSq x.2 := hx.2
      rw [h0, Complex.normSq_zero] at h2
      linarith
  unfold coordE
  split_ifs
  · exact hz
  · simpa using hz

/- English proof (translation)
Simplify using `[coordE, zE, M.vz]`.
-/
theorem coordE_vz (x : E r) : coordE (M.vz : M.Var r) x = x.2 := by simp [coordE, zE, M.vz]

/- English proof (translation)
Simplify using `[coordE, zE, M.vzb]`.
-/
theorem coordE_vzb (x : E r) : coordE (M.vzb : M.Var r) x = conj x.2 := by simp [coordE, zE, M.vzb]

def ggQ (r : ℕ) (TT : ℝ) : SmQ r TT := (anQ r TT).gg TT

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [ggQ, DAlg.gg, anQ, coordQ]`.
-/
theorem gg_apply (q : Qp r TT) : ((ggQ r TT : SmQ r TT) : Qp r TT → ℂ) q =
    coordE M.vz q.1 * coordE M.vzb q.1 - (TT : ℂ) := by
  first
  | rfl
  | simp [ggQ, DAlg.gg, anQ, coordQ]

/- English proof (translation)
Rewrite using `[gg_apply, coordE_vz, coordE_vzb, Complex.mul_conj]`. Introduce `h`. Establish `h2 : (Complex.normSq q.1.2 : ℂ) = (TT : ℂ)` using `sub_eq_zero.1 h`. Establish `h3 : Complex.normSq q.1.2 = TT` using `by exact_mod_cast h2`. Establish `h4 : TT < Complex.normSq q.1.2` using `q.2.2`.

Conclude with `(ne_of_gt h4) h3`.
-/
theorem gg_ne (q : Qp r TT) : ((ggQ r TT : SmQ r TT) : Qp r TT → ℂ) q ≠ 0 := by
  rw [gg_apply, coordE_vz, coordE_vzb, Complex.mul_conj]
  intro h
  have h2 : (Complex.normSq q.1.2 : ℂ) = (TT : ℂ) := sub_eq_zero.1 h
  have h3 : Complex.normSq q.1.2 = TT := by exact_mod_cast h2
  have h4 : TT < Complex.normSq q.1.2 := q.2.2
  exact (ne_of_gt h4) h3

end

end Formalism.FourierDecayAlt.P.MAx1.An

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt MAx1.An
open scoped ComplexConjugate

/- English proof (translation)
Introduce `r TT v f g`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Simplify using `only [Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply, eulerQ_apply]`. Rewrite using `[ext_mul, show ext (f : Qp r TT → ℂ) * ext (g : Qp r TT → ℂ) = fun y => ext (f : Qp r TT → ℂ) y * ext (g : Qp r TT → ℂ) y from rfl, wirt_mul v (ext_smooth_diff f.2 q.1 q.2) (ext_smooth_diff g.2 q.1 q.2), ext_of_mem _ q.2, ext_of_mem _ q.2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem analytic_leibniz : Formalism.FourierDecayAlt.MA.AnLeibniz := by
  intro r TT v f g
  apply Subtype.ext; funext q
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Pi.add_apply, Pi.mul_apply, eulerQ_apply]
  rw [ext_mul, show ext (f : Qp r TT → ℂ) * ext (g : Qp r TT → ℂ) =
      fun y => ext (f : Qp r TT → ℂ) y * ext (g : Qp r TT → ℂ) y from rfl,
    wirt_mul v (ext_smooth_diff f.2 q.1 q.2) (ext_smooth_diff g.2 q.1 q.2),
    ext_of_mem _ q.2, ext_of_mem _ q.2]
  ring

/- English proof (translation)
Introduce `r TT v w`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Rewrite using `[eulerQ_apply]`. Establish `h1 : ext ((coordQ w : SmQ r TT) : Qp r TT → ℂ) =ᶠ[nhds q.1] coordE w` using `ext_comp_ev (coordE w) q.2`.

Rewrite using `[wirt_congr v h1, wirt_coord]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Simplify using `[h]`.
-/
theorem analytic_coordinates : Formalism.FourierDecayAlt.MA.AnCoord := by
  intro r TT v w
  apply Subtype.ext; funext q
  rw [eulerQ_apply]
  have h1 : ext ((coordQ w : SmQ r TT) : Qp r TT → ℂ) =ᶠ[nhds q.1] coordE w :=
    ext_comp_ev (coordE w) q.2
  rw [wirt_congr v h1, wirt_coord]
  by_cases h : v = w
  · subst h; simp; rfl
  · simp [h]

/- English proof (translation)
Introduce `r TT v w`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `f`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`.

Simplify using `only [Module.End.mul_apply]`. Rewrite using `[euler_euler, euler_euler]`. Distinguish the cases in `h : v = w`. Substitute `h` using the available equality. Both sides reduce to the same expression.

Rewrite using `[if_neg h, if_neg (Ne.symm h), wirt_wirt v w (Qset_open r TT) (f.2 : ContDiffOn ℝ sm (ext (f : Qp r TT → ℂ)) (Qset r TT)) q.2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem analytic_commutation : Formalism.FourierDecayAlt.MA.AnComm := by
  intro r TT v w
  apply LinearMap.ext; intro f
  apply Subtype.ext; funext q
  simp only [Module.End.mul_apply]
  rw [euler_euler, euler_euler]
  by_cases h : v = w
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h),
      wirt_wirt v w (Qset_open r TT) (f.2 : ContDiffOn ℝ sm (ext (f : Qp r TT → ℂ)) (Qset r TT)) q.2]
    ring

/- English proof (translation)
Introduce `r TT hTT`. Conclude with `⟨fun v => isUnit_of_ne _ fun q => coordE_ne q.2 hTT v, isUnit_of_ne (ggQ r TT) fun q => gg_ne q⟩`.
-/
theorem analytic_units_hold : Formalism.FourierDecayAlt.MA.AnUnits := by
  intro r TT hTT
  exact ⟨fun v => isUnit_of_ne _ fun q => coordE_ne q.2 hTT v, isUnit_of_ne (ggQ r TT) fun q => gg_ne q⟩

/- English proof (translation)
Introduce `r TT`. Establish `hx : ((fun _ => (1 : ℂ)), (((|TT| + 1 : ℝ)) : ℂ)) ∈ Qset r TT`. Use `⟨fun l => one_ne_zero, ?_⟩` and prove the remaining obligations. Use `show TT < Complex.normSq (((|TT| + 1 : ℝ)) : ℂ)`. Rewrite using `[Complex.normSq_ofReal]`.

Use polynomial arithmetic with `[abs_nonneg TT, le_abs_self TT]`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun f : SmQ r TT => (f : Qp r TT → ℂ) ⟨_, hx⟩) h`. Simplify using `at h1`.
-/
theorem analytic_nontrivial : Formalism.FourierDecayAlt.MA.AnNontrivial := by
  intro r TT
  have hx : ((fun _ => (1 : ℂ)), (((|TT| + 1 : ℝ)) : ℂ)) ∈ Qset r TT := by
    refine ⟨fun l => one_ne_zero, ?_⟩
    show TT < Complex.normSq (((|TT| + 1 : ℝ)) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg TT, le_abs_self TT]
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h1 := congrArg (fun f : SmQ r TT => (f : Qp r TT → ℂ) ⟨_, hx⟩) h
  simp at h1

/- English proof (translation)
Introduce `hL hC hCm hU hN r TT hTT`. Conclude with `⟨hL r TT, hC r TT, hCm r TT, (hU r TT hTT).1, (hU r TT hTT).2, hN r TT⟩`.
-/
theorem analytic_laws_of_parts : Formalism.FourierDecayAlt.MA.AnLawsOfParts := by
  intro hL hC hCm hU hN r TT hTT
  exact ⟨hL r TT, hC r TT, hCm r TT, (hU r TT hTT).1, (hU r TT hTT).2, hN r TT⟩

/- English proof (translation)
The claim follows from `analytic_laws_of_parts analytic_leibniz analytic_coordinates analytic_commutation analytic_units_hold analytic_nontrivial`.
-/
theorem analytic_laws : Formalism.FourierDecayAlt.MA.AnLaws :=
  analytic_laws_of_parts analytic_leibniz analytic_coordinates analytic_commutation analytic_units_hold
    analytic_nontrivial

end Formalism.FourierDecayAlt.P

end

section
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.MAx1

open Formalism.FourierDecayAlt Finset Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism.FourierDecayAlt.M hiding A sc kap pA pbA cA ciA cbA cbiA zA ziA zbA zbiA ggA ggiA nabA nabsA IsModelLevel SS l0A m0A xA weightedSumBis S12 S4 t22 t21 t12 t11 QQr eeA startM siteA FrameConcl Pr Op mulOp fnP mk cP ciP cbP cbiP zP ziP zbP zbiP ggP ggiP pP pbP dzP dzbP gg coord euler lA mA fnsA zfnsA sitesFrom QQlev LevFns LevP LevPb LevPP LevNab LevNabs StarGens SSScalar SSShift SSNorm SSComm SSMixed NabSS Curvature QQNormal QQHerm QQRTTEntries QQRTT QQRTTOfEntries QQDet T21Commute QQLeading QQZeta StartIsStart StartOK LevelExists LevelStar SitesOKM ChainM LowerCommutes LowerStart StartIsStartAssemble StartAssemble LevelAssemble ModelFrame ModelAssemble CutAdm
open Formalism.FourierDecayAlt.MA

/- English proof (translation)
The claim follows from `startIsStartAssemble qQHerm qQRTT qQDet`.
-/
theorem startIsStart : StartIsStart := startIsStartAssemble qQHerm qQRTT qQDet

/- English proof (translation)
The claim follows from `startAssemble startIsStart lower_left_commute sSScalar sSShift rho_raise`.
-/
theorem startOK : StartOK := startAssemble startIsStart lower_left_commute sSScalar sSShift rho_raise

/- English proof (translation)
Use `show Ring.inverse f = f⁻¹`. Rewrite using `[Ring.inverse_eq_inv']`.
-/
theorem hahn_inv {r : ℕ} (f : M.Fn r) : (hahn r).inv f = f⁻¹ := by
  show Ring.inverse f = f⁻¹
  rw [Ring.inverse_eq_inv']

end Formalism.FourierDecayAlt.P.MAx1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA MAx1

/- English proof (translation)
Introduce `r TT`. Establish `hL` using `Formalism.FourierDecayAlt.P.euler_leibniz`. Establish `hC` using `Formalism.FourierDecayAlt.P.euler_coordinates`. Establish `hM` using `Formalism.FourierDecayAlt.P.euler_commute`. Establish `hN` using `Formalism.FourierDecayAlt.P.function_nonzero`.

Use `⟨fun v f g => hL r v f g, fun v w => (hC r v w 0).1, fun v w => hM r v w, fun v => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `isUnit_iff_ne_zero.2 (hN r v 0).1`. Conclude with `isUnit_iff_ne_zero.2 (hN r M.vz TT).2`. Conclude with `inferInstanceAs (Nontrivial (M.Fn r))`.
-/
theorem hahn_laws_hold : Formalism.FourierDecayAlt.MA.HahnLaws := by
  intro r TT
  have hL := Formalism.FourierDecayAlt.P.euler_leibniz
  have hC := Formalism.FourierDecayAlt.P.euler_coordinates
  have hM := Formalism.FourierDecayAlt.P.euler_commute
  have hN := Formalism.FourierDecayAlt.P.function_nonzero
  refine ⟨fun v f g => hL r v f g, fun v w => (hC r v w 0).1, fun v w => hM r v w, fun v => ?_, ?_, ?_⟩
  · exact isUnit_iff_ne_zero.2 (hN r v 0).1
  · exact isUnit_iff_ne_zero.2 (hN r M.vz TT).2
  · exact inferInstanceAs (Nontrivial (M.Fn r))

/- English proof (translation)
Introduce `P`. Establish `hi : ∀ f : (hahn P.r).R, (hahn P.r).inv f = @Inv.inv (M.Fn P.r) _ f` using `fun f => hahn_inv f`. Establish `e_ci : ∀ l, ciA P (hahn P.r) l = M.ciA P l` using `fun l => by`. Simplify using `only [ciA, M.ciA, sc, M.sc, DAlg.ciP, M.ciP, hi]`. Both sides reduce to the same expression.

Establish `e_cbi : ∀ l, cbiA P (hahn P.r) l = M.cbiA P l` using `fun l => by`. Simplify using `only [cbiA, M.cbiA, sc, M.sc, DAlg.cbiP, M.cbiP, hi]`. Both sides reduce to the same expression. Establish `e_zi : ziA P (hahn P.r) = M.ziA P` using `by simp only [ziA, M.ziA, sc, M.sc, DAlg.ziP, M.ziP, hi]; rfl`. Establish `e_zbi : zbiA P (hahn P.r) = M.zbiA P` using `by simp only [zbiA, M.zbiA, sc, M.sc, DAlg.zbiP, M.zbiP, hi]; rfl`.

Establish `e_ggi : ggiA P (hahn P.r) = M.ggiA P` using `by simp only [ggiA, M.ggiA, sc, M.sc, DAlg.ggiP, M.ggiP, hi]; rfl`. Establish `e_dz : (hahn P.r).dzP = M.dzP` using `by simp only [DAlg.dzP, M.dzP, hi]; rfl`. Establish `e_dzb : (hahn P.r).dzbP = M.dzbP` using `by simp only [DAlg.dzbP, M.dzbP, hi]; rfl`. Establish `e_ggiP : (hahn P.r).ggiP P.TT = M.ggiP P.TT` using `by simp only [DAlg.ggiP, M.ggiP, hi]; rfl`. Establish `e_nab : nabA P (hahn P.r) = M.nabA P` using `by simp only [nabA, M.nabA, e_dz, e_ggiP]; rfl`.

Establish `e_nabs : nabsA P (hahn P.r) = M.nabsA P` using `by simp only [nabsA, M.nabsA, e_dzb, e_ggiP]; rfl`. Establish `e_l0 : ∀ Y, l0A P (hahn P.r) Y = M.l0A P Y` using `fun Y => by simp only [l0A, M.l0A, e_nab, e_ggi]; rfl`. Establish `e_m0 : ∀ Y, m0A P (hahn P.r) Y = M.m0A P Y` using `fun Y => by simp only [m0A, M.m0A, e_nabs, e_ggi]; rfl`. Establish `e_QQ : ∀ Y, QQr P (hahn P.r) Y = M.QQr P Y` using `fun Y => by`. Simplify using `only [QQr, M.QQr, t11, M.t11, t12, M.t12, t21, M.t21, t22, M.t22, e_l0, e_m0, e_ggi]`.

Both sides reduce to the same expression. Establish `e_ee : eeA P (hahn P.r) = M.eeA P` using `by funext Y; simp only [eeA, M.eeA, e_zbi]; rfl`. Use `⟨fun l => rfl, fun l => rfl, fun l => rfl, e_ci, fun l => rfl, e_cbi, rfl, e_zi, rfl, e_zbi, rfl, e_ggi, e_nab, e_nabs, fun l => rfl, fun l => ?_⟩` and prove the remaining obligations. Simplify using `only [startM, M.startM, e_QQ, e_ee]`. Both sides reduce to the same expression.
-/
theorem hahn_joint : Formalism.FourierDecayAlt.MA.HahnJoint := by
  intro P
  have hi : ∀ f : (hahn P.r).R, (hahn P.r).inv f = @Inv.inv (M.Fn P.r) _ f := fun f => hahn_inv f
  have e_ci : ∀ l, ciA P (hahn P.r) l = M.ciA P l := fun l => by
    simp only [ciA, M.ciA, sc, M.sc, DAlg.ciP, M.ciP, hi]; rfl
  have e_cbi : ∀ l, cbiA P (hahn P.r) l = M.cbiA P l := fun l => by
    simp only [cbiA, M.cbiA, sc, M.sc, DAlg.cbiP, M.cbiP, hi]; rfl
  have e_zi : ziA P (hahn P.r) = M.ziA P := by simp only [ziA, M.ziA, sc, M.sc, DAlg.ziP, M.ziP, hi]; rfl
  have e_zbi : zbiA P (hahn P.r) = M.zbiA P := by simp only [zbiA, M.zbiA, sc, M.sc, DAlg.zbiP, M.zbiP, hi]; rfl
  have e_ggi : ggiA P (hahn P.r) = M.ggiA P := by simp only [ggiA, M.ggiA, sc, M.sc, DAlg.ggiP, M.ggiP, hi]; rfl
  have e_dz : (hahn P.r).dzP = M.dzP := by simp only [DAlg.dzP, M.dzP, hi]; rfl
  have e_dzb : (hahn P.r).dzbP = M.dzbP := by simp only [DAlg.dzbP, M.dzbP, hi]; rfl
  have e_ggiP : (hahn P.r).ggiP P.TT = M.ggiP P.TT := by simp only [DAlg.ggiP, M.ggiP, hi]; rfl
  have e_nab : nabA P (hahn P.r) = M.nabA P := by simp only [nabA, M.nabA, e_dz, e_ggiP]; rfl
  have e_nabs : nabsA P (hahn P.r) = M.nabsA P := by simp only [nabsA, M.nabsA, e_dzb, e_ggiP]; rfl
  have e_l0 : ∀ Y, l0A P (hahn P.r) Y = M.l0A P Y := fun Y => by simp only [l0A, M.l0A, e_nab, e_ggi]; rfl
  have e_m0 : ∀ Y, m0A P (hahn P.r) Y = M.m0A P Y := fun Y => by simp only [m0A, M.m0A, e_nabs, e_ggi]; rfl
  have e_QQ : ∀ Y, QQr P (hahn P.r) Y = M.QQr P Y := fun Y => by
    simp only [QQr, M.QQr, t11, M.t11, t12, M.t12, t21, M.t21, t22, M.t22, e_l0, e_m0, e_ggi]; rfl
  have e_ee : eeA P (hahn P.r) = M.eeA P := by funext Y; simp only [eeA, M.eeA, e_zbi]; rfl
  refine ⟨fun l => rfl, fun l => rfl, fun l => rfl, e_ci, fun l => rfl, e_cbi, rfl, e_zi, rfl, e_zbi, rfl, e_ggi, e_nab,
    e_nabs, fun l => rfl, fun l => ?_⟩
  simp only [startM, M.startM, e_QQ, e_ee]
  rfl

/- English proof (translation)
Introduce `P D hD`. Establish `: Fact (D.Laws P.TT)` using `⟨hD⟩`. Conclude with `levelExists P D`.
-/
theorem level_exists_alt : Formalism.FourierDecayAlt.MA.LevelExistsD := by
  intro P D hD
  have : Fact (D.Laws P.TT) := ⟨hD⟩
  exact levelExists P D

/- English proof (translation)
Introduce `P D hD L hL`. Establish `: Fact (D.Laws P.TT)` using `⟨hD⟩`. Conclude with `levelStar P D L hL`.
-/
theorem level_star_holds : Formalism.FourierDecayAlt.MA.LevelStarD := by
  intro P D hD L hL
  have : Fact (D.Laws P.TT) := ⟨hD⟩
  exact levelStar P D L hL

/- English proof (translation)
Introduce `P hP D hD l L hL`. Establish `: Fact (D.Laws P.TT)` using `⟨hD⟩`. Conclude with `startOK P D hP l L hL`.
-/
theorem start_admissible : Formalism.FourierDecayAlt.MA.StartOKD := by
  intro P hP D hD l L hL
  have : Fact (D.Laws P.TT) := ⟨hD⟩
  exact startOK P D hP l L hL

/- English proof (translation)
Introduce `P D hD l`. Establish `: Fact (D.Laws P.TT)` using `⟨hD⟩`. Rewrite using `[sites_eq]`. Conclude with `sitesOKM P D l`.
-/
theorem sites_admissible : Formalism.FourierDecayAlt.MA.SitesOKD := by
  intro P D hD l
  have : Fact (D.Laws P.TT) := ⟨hD⟩
  rw [sites_eq]
  exact sitesOKM P D l

/- English proof (translation)
Introduce `P D l S _ _ w`. Conclude with `Iff.rfl`.
-/
theorem admissible_joint_alt : Formalism.FourierDecayAlt.MA.AdmJoint := by
  intro P D l S _ _ w
  exact Iff.rfl

/- English proof (translation)
Introduce `hSign hQ hQS hCPos hCPosCut hFA hFW hCD hTy hR hCA hAJ hLE hLS hSt P hP l hl hlk D hD`. Take `⟨L, hL⟩` from `hLE P D hD`. Establish `hstar` using `hLS P D hD L hL`. Establish `hst` using `hSt P hP D hD l L hL`. Use `⟨L, hL, hstar, hst, ?_⟩` and prove the remaining obligations.

Introduce `S _ _ w hw`. Establish `hadm : Fr.admitted (startM P D l) w` using `(hAJ P D l S w).2 (hCA hSign hQ hQS hTy hR P hP l hl hlk S w hw)`. Take `⟨-, -, f1, -, -⟩` from `hFW (A P D) S P.r L (startM P D l) w hstar hst hadm`. Use `⟨hFA (A P D) S P.r L (startM P D l) w hstar hst hadm, f1, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hCD (A P D) S P.r L (startM P D l) (M.Ty P) (kap P D) (M.x0 P l) (fun _ => rfl) (fun _ => rfl) w).2.2`.

Introduce `e π`. Conclude with `hCPosCut hSign hQ hQS hCPos S P.k P.u P.u' (M.rho P π) l P.T P.T' w hl hlk (hTy P hP π) hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e`.
-/
theorem model_frame_of_parts : Formalism.FourierDecayAlt.MA.ModelFrameDOfParts := by
  intro hSign hQ hQS hCPos hCPosCut hFA hFW hCD hTy hR hCA hAJ hLE hLS hSt P hP l hl hlk D hD
  obtain ⟨L, hL⟩ := hLE P D hD
  have hstar := hLS P D hD L hL
  have hst := hSt P hP D hD l L hL
  refine ⟨L, hL, hstar, hst, ?_⟩
  intro S _ _ w hw
  have hadm : Fr.admitted (startM P D l) w := (hAJ P D l S w).2 (hCA hSign hQ hQS hTy hR P hP l hl hlk S w hw)
  obtain ⟨-, -, f1, -, -⟩ := hFW (A P D) S P.r L (startM P D l) w hstar hst hadm
  refine ⟨hFA (A P D) S P.r L (startM P D l) w hstar hst hadm, f1, ?_, ?_⟩
  · exact (hCD (A P D) S P.r L (startM P D l) (M.Ty P) (kap P D) (M.x0 P l) (fun _ => rfl) (fun _ => rfl) w).2.2
  · intro e π
    exact hCPosCut hSign hQ hQS hCPos S P.k P.u P.u' (M.rho P π) l P.T P.T' w hl hlk (hTy P hP π)
      hP.T_pos hP.T'_pos hw.2.1 hw.2.2 e

/- English proof (translation)
The claim follows from `model_frame_of_parts interlacing_sign q_positive_interlacing q_positive_shift cPos_true c_pos_truncated frame_of_admissible_word frame_eq_word_module c_diagonal types_interlace realPoints_statement cut_admissible admissible_joint_alt level_exists_alt level_star_holds start_admiss …`.
-/
theorem model_frame_algebra : Formalism.FourierDecayAlt.MA.ModelFrameD :=
  model_frame_of_parts interlacing_sign q_positive_interlacing q_positive_shift cPos_true
    c_pos_truncated frame_of_admissible_word frame_eq_word_module c_diagonal types_interlace realPoints_statement
    cut_admissible admissible_joint_alt level_exists_alt level_star_holds start_admissible

/- English proof (translation)
Introduce `hF hA P hP l hl hlk`. Establish `hT : 0 ≤ P.TT` using `by unfold M.Par.TT; exact (mul_pos hP.T_pos hP.T'_pos).le`. Conclude with `hF P hP l hl hlk (DQ P) (hA P.r P.TT hT)`.
-/
theorem model_frame_analytic_of_parts : Formalism.FourierDecayAlt.MA.ModelFrameAnOfParts := by
  intro hF hA P hP l hl hlk
  have hT : 0 ≤ P.TT := by unfold M.Par.TT; exact (mul_pos hP.T_pos hP.T'_pos).le
  exact hF P hP l hl hlk (DQ P) (hA P.r P.TT hT)

/- English proof (translation)
The claim follows from `model_frame_analytic_of_parts model_frame_algebra analytic_laws`.
-/
theorem model_frame_analytic : Formalism.FourierDecayAlt.MA.ModelFrameAn :=
  model_frame_analytic_of_parts model_frame_algebra analytic_laws

end Formalism.FourierDecayAlt.P

end
