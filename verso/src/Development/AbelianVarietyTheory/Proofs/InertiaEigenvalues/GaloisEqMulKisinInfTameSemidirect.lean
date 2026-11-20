import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinftyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisPowFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversOfActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoversActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemKummerTowerUnramifiedOfCoversOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixingKunrMemInertiaModFieldInfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummerStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TameCover

section
variable {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l)
  [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul o w => rw [galOA_tmul, galOA_tmul, galOA_tmul, GlobalTheory.RingBasics.σA_mul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem galOA_mul' {O : Type} [CommRing O] [Algebra ℤ_[l] O] (g h : GQ l) (x : OA l O) :
    galOA O (g * h) x = galOA O g (galOA O h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => rw [galOA_tmul, galOA_tmul, galOA_tmul, GlobalTheory.RingBasics.σA_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

def actA (γ : TameGal ↥LL.1 l e a) (f : ZMod a → A ↥(OL LL) ↥LL.1) : ZMod a → A ↥(OL LL) ↥LL.1 :=
  fun τ => ⟨ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) τ, Rot.ringAct_mem rot_A γ (fun σ => (f σ).2) τ⟩

/- English proof (translation)
Introduce `f f'' hf''`. Establish `h1` using `hk' f (actA LL γ' f) (fun τ => rfl)`. Establish `h2` using `hk (actA LL γ' f) f'' (fun τ => by`. Rewrite using `[hf'' τ, map_mul]`. Use the proof step `rfl)`.

Rewrite using `[galOA_mul', h1, h2]`.
-/
theorem covers_mul {k k' : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hk : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hk' : Covers ↥LL.1 (thetaW a LL) ϖ k' γ') :
    Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ') := by
  intro f f'' hf''
  have h1 := hk' f (actA LL γ' f) (fun τ => rfl)
  have h2 := hk (actA LL γ' f) f'' (fun τ => by
    rw [hf'' τ, map_mul]
    rfl)
  rw [galOA_mul', h1, h2]

/- English proof (translation)
Introduce `f f' hf'`. Establish `: f' = f` using `funext fun τ => Subtype.ext (by rw [hf' τ, map_one]; rfl)`. Rewrite using `[this]`. Conclude with `ϖ.galOA_iTot (thetaW a LL) ↥LL.1 hk f`.
-/
theorem covers_of_mem {k : GQ l} (hk : k ∈ ϖ.GfieldInf a) :
    Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) := by
  intro f f' hf'
  have : f' = f := funext fun τ => Subtype.ext (by rw [hf' τ, map_one]; rfl)
  rw [this]
  exact ϖ.galOA_iTot (thetaW a LL) ↥LL.1 hk f

/- English proof (translation)
Establish `key : ∀ f : ZMod a → A ↥(OL LL) ↥LL.1, ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) = ringAct γ' (fun σ => (f σ : PowerSeries ↥LL.1))`. Introduce `f`. Establish `h` using `(hγ f (actA LL γ f) (fun _ => rfl)).symm.trans (hγ' f (actA LL γ' f) (fun _ => rfl))`. Establish `h2` using `ϖ.iTot_injective (thetaW a LL) ↥LL.1 h`. Use function extensionality and compare the values at `τ`.

Conclude with `congrArg Subtype.val (congrFun h2 τ)`. Establish `hs : γ.shift = γ'.shift`. Assume the negation of the conclusion as `hne`. Establish `h` using `congrFun (key fun σ => if σ = 0 then 1 else 0) γ.shift`. Simplify using `only [ringAct_apply, sub_self] at h`.

Rewrite `h` using `[if_neg (sub_ne_zero.2 hne)]`. Simplify using `at h`. Establish `hl : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) = ((γ'.left : (↥LL.1)ˣ) : ↥LL.1)`. Establish `h` using `congrArg (fun F => coeff 1 (F 0)) (key fun _ => uIn _)`. Establish `hu : ((uIn (A ↥(OL LL) ↥LL.1) : A ↥(OL LL) ↥LL.1) : PowerSeries ↥LL.1) = X` using `rfl`.

Simplify using `only [hu, ringAct_X, coeff_C_mul, coeff_one_X, mul_one] at h`. Simplify `h` using `[TameGal.root]`. Use `SemidirectProduct.ext (Subtype.ext (Units.ext hl)) ?_` and prove the remaining obligations. Conclude with `congrArg Multiplicative.ofAdd hs`.
-/
theorem covers_unique {k : GQ l} {γ γ' : TameGal ↥LL.1 l e a}
    (hγ : Covers ↥LL.1 (thetaW a LL) ϖ k γ) (hγ' : Covers ↥LL.1 (thetaW a LL) ϖ k γ') : γ = γ' := by
  have key : ∀ f : ZMod a → A ↥(OL LL) ↥LL.1,
      ringAct γ (fun σ => (f σ : PowerSeries ↥LL.1)) = ringAct γ' (fun σ => (f σ : PowerSeries ↥LL.1)) := by
    intro f
    have h := (hγ f (actA LL γ f) (fun _ => rfl)).symm.trans (hγ' f (actA LL γ' f) (fun _ => rfl))
    have h2 := ϖ.iTot_injective (thetaW a LL) ↥LL.1 h
    funext τ
    exact congrArg Subtype.val (congrFun h2 τ)
  have hs : γ.shift = γ'.shift := by
    by_contra hne
    have h := congrFun (key fun σ => if σ = 0 then 1 else 0) γ.shift
    simp only [ringAct_apply, sub_self] at h
    rw [if_neg (sub_ne_zero.2 hne)] at h
    simp at h
  have hl : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) = ((γ'.left : (↥LL.1)ˣ) : ↥LL.1) := by
    have h := congrArg (fun F => coeff 1 (F 0)) (key fun _ => uIn _)
    have hu : ((uIn (A ↥(OL LL) ↥LL.1) : A ↥(OL LL) ↥LL.1) : PowerSeries ↥LL.1) = X := rfl
    simp only [hu, ringAct_X, coeff_C_mul, coeff_one_X, mul_one] at h
    simpa [TameGal.root] using h
  refine SemidirectProduct.ext (Subtype.ext (Units.ext hl)) ?_
  exact congrArg Multiplicative.ofAdd hs

omit [HasUnr a LL] in
/- English proof (translation)
Take `⟨ζ0, h0⟩` from `TameDescentExponentData.prim (K := ↥LL.1) l a (e := e)`. Establish `h1 : IsPrimitiveRoot ((ζ0 : ↥LL.1) : Om l) e` using `h0.map_of_injective (f := LL.1.val) Subtype.val_injective`. Take `⟨i, -, hi⟩` from `h1.eq_pow_of_pow_eq_one hζ`. Use `⟨rootsOfUnity.mkOfPowEq (ζ0 ^ i) (by rw [← pow_mul, mul_comm, pow_mul, h0.pow_eq_one, one_pow]), ?_⟩` and prove the remaining obligations. Rewrite using `[rootsOfUnity.val_mkOfPowEq_coe, ← hi]`.

Both sides reduce to the same expression.
-/
theorem lift_root (a : ℕ) [TameDescentExponentData ↥LL.1 l e a] (ζ : Om l) (hζ : ζ ^ e = 1) :
    ∃ ζK : rootsOfUnity e ↥LL.1, (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) = ζ := by
  obtain ⟨ζ0, h0⟩ := TameDescentExponentData.prim (K := ↥LL.1) l a (e := e)
  have h1 : IsPrimitiveRoot ((ζ0 : ↥LL.1) : Om l) e := h0.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one hζ
  refine ⟨rootsOfUnity.mkOfPowEq (ζ0 ^ i) (by rw [← pow_mul, mul_comm, pow_mul, h0.pow_eq_one, one_pow]), ?_⟩
  rw [rootsOfUnity.val_mkOfPowEq_coe, ← hi]
  rfl

end

end GlobalTheory.TameCover
end

namespace GlobalTheory.TameCover

/- English proof (translation)
Introduce `l _ a e _ _ ϖ LL _ _`. Establish `hsucc : e + 1 = l ^ a` using `TameDescentExponentData.succ_eq (↥LL.1) (l := l) (e := e) (a := a)`. Establish `hroot_mem : ∀ x : Om l, x ^ l ^ a = x → x ∈ (ϖ.field a).1` using `fun x hx => ϖ.Kunr_le_field a (IntermediateField.subset_adjoin _ _ hx)`. Establish `hfix : ∀ h ∈ GK (ϖ.field a), ∀ x ∈ (ϖ.field a).1, h x = x` using `fun h hh x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx`. Use `⟨GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc, ?_, ?_, fun k γ γ' => covers_unique ϖ LL, fun k k' γ γ' => covers_mul ϖ LL, fun k => ⟨GlobalTheory.T.mem_kummerTowerUnramified_of_covers_one l a e ϖ LL k, covers_of_mem ϖ LL⟩, ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Take `⟨m, hm⟩` from `GlobalTheory.T.exists_apply_eq_pow_of_pow_pow_eq l a k`. Establish `hπ : ϖ.seq 0 ≠ 0` using `ϖ.seq_ne_zero 0`. Establish `hke : k (ϖ.seq 0 ^ e) = ϖ.seq 0 ^ e` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩)`. Establish `hζ : (k (ϖ.seq 0) / ϖ.seq 0) ^ e = 1`.

Rewrite using `[div_pow, ← map_pow, hke, div_self (pow_ne_zero _ hπ)]`. Take `⟨ζK, hζK⟩` from `lift_root LL a _ hζ`. Use `⟨⟨ζK, Multiplicative.ofAdd m⟩, GlobalTheory.T.covers_of_action' l a e ϖ LL _ k hk hm ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `k (ϖ.seq 0) = (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0`. Rewrite using `[hζK, div_mul_cancel₀ _ hπ]`.

Introduce `γ`. Establish `hζ : ((((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l)) ^ e = 1`. Establish `h1 : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 γ.left.2, Units.val_one]`. Rewrite using `[← IntermediateField.coe_pow, h1]`.

Both sides reduce to the same expression. Take `⟨g, hg1, hg2⟩` from `GlobalTheory.T.exists_galois_prescribed_unramified_kummer l a e ϖ hsucc γ.shift _ hζ`. Take `⟨h, hh, k, hk, rfl⟩` from `GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc g`. Establish `hinj : Function.Injective h` using `h.injective`. Use `⟨k, hk, GlobalTheory.T.covers_of_action' l a e ϖ LL γ k hk (fun x hx => hinj ?_) (hinj ?_)⟩` and prove the remaining obligations.

Establish `h1` using `hg1 x hx`. Establish `h2 : (x ^ l ^ γ.shift.val) ^ l ^ a = x ^ l ^ γ.shift.val`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hx]`. Rewrite using `[hfix h hh _ (hroot_mem _ h2)]`. Conclude with `h1`.

Establish `hz : (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) ^ l ^ a = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l)`. Rewrite using `[← hsucc, pow_succ, hζ, one_mul]`. Rewrite using `[hfix h hh _ (mul_mem (hroot_mem _ hz) (ϖ.pi_mem_field a))]`. Conclude with `hg2`. Introduce `k ζ hk`.

Take `⟨hr, -⟩` from `GlobalTheory.T.action_of_covers l a e ϖ LL k _ hk`. Establish `hr' : ∀ x : Om l, x ^ l ^ a = x → k x = x` using `fun x hx => by`. Rewrite using `[hr x hx]`. Simplify using the standard rewrite rules. Take `⟨k', hk', h, hh, hkh⟩` from `GlobalTheory.T.fixing_kunr_mem_inertia_mod_fieldInf l a e ϖ hsucc k hr'`.

Establish `hc : Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a)`. Use `covers_mul ϖ LL hk (covers_of_mem ϖ LL hh)` as an intermediate fact. Rewrite `this` using `[mul_one, ← hkh]`. Then use the resulting hypothesis. Use `⟨k', hk', hc, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.T.action_of_covers l a e ϖ LL _ _ hc).2]`.

Both sides reduce to the same expression.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g : GQ l, ∃ h ∈ GK (ϖ.field a), ∃ k ∈ ϖ.GKinf, g = h * k) ∧ (∀ k ∈ ϖ.GKinf, ∃ γ, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ γ : TameGal ↥LL.1 l e a, ∃ k ∈ ϖ.GKinf, Covers ↥LL.1 (thetaW a LL) ϖ k γ) ∧ (∀ (k : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k γ' → γ = γ') ∧ (∀ (k k' : GQ l) (γ γ' : TameGal ↥LL.1 l e a), Covers ↥LL.1 (thetaW a LL) ϖ k γ → Covers ↥LL.1 (thetaW a LL) ϖ k' γ' → Covers ↥LL.1 (thetaW a LL) ϖ (k * k') (γ * γ')) ∧ (∀ k : GQ l, Covers ↥LL.1 (thetaW a LL) ϖ k (1 : TameGal ↥LL.1 l e a) ↔ k ∈ ϖ.GfieldInf a) ∧ ∀ (k : GQ l) (ζ : rootsOfUnity e ↥LL.1), Covers ↥LL.1 (thetaW a LL) ϖ k (TameGal.inertia ζ : TameGal ↥LL.1 l e a) → ∃ k' ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) ∧ (((ζ : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by
  intro l _ a e _ _ ϖ LL _ _
  have hsucc : e + 1 = l ^ a := TameDescentExponentData.succ_eq (↥LL.1) (l := l) (e := e) (a := a)

  have hroot_mem : ∀ x : Om l, x ^ l ^ a = x → x ∈ (ϖ.field a).1 := fun x hx =>
    ϖ.Kunr_le_field a (IntermediateField.subset_adjoin _ _ hx)
  have hfix : ∀ h ∈ GK (ϖ.field a), ∀ x ∈ (ϖ.field a).1, h x = x := fun h hh x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).1 hh x hx
  refine ⟨GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc, ?_, ?_, fun k γ γ' => covers_unique ϖ LL, fun k k' γ γ' => covers_mul ϖ LL,
    fun k => ⟨GlobalTheory.T.mem_kummerTowerUnramified_of_covers_one l a e ϖ LL k, covers_of_mem ϖ LL⟩, ?_⟩
  · intro k hk
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_apply_eq_pow_of_pow_pow_eq l a k
    have hπ : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
    have hke : k (ϖ.seq 0 ^ e) = ϖ.seq 0 ^ e :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hk _ (IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩)
    have hζ : (k (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, hke, div_self (pow_ne_zero _ hπ)]
    obtain ⟨ζK, hζK⟩ := lift_root LL a _ hζ
    refine ⟨⟨ζK, Multiplicative.ofAdd m⟩, GlobalTheory.T.covers_of_action' l a e ϖ LL _ k hk hm ?_⟩
    change k (ϖ.seq 0) = (((ζK : (↥LL.1)ˣ) : ↥LL.1) : Om l) * ϖ.seq 0
    rw [hζK, div_mul_cancel₀ _ hπ]
  · intro γ
    have hζ : ((((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l)) ^ e = 1 := by
      have h1 : ((γ.left : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 γ.left.2, Units.val_one]
      rw [← IntermediateField.coe_pow, h1]
      rfl
    obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.exists_galois_prescribed_unramified_kummer l a e ϖ hsucc γ.shift _ hζ
    obtain ⟨h, hh, k, hk, rfl⟩ := GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ hsucc g
    have hinj : Function.Injective h := h.injective
    refine ⟨k, hk, GlobalTheory.T.covers_of_action' l a e ϖ LL γ k hk (fun x hx => hinj ?_) (hinj ?_)⟩
    · have h1 := hg1 x hx
      have h2 : (x ^ l ^ γ.shift.val) ^ l ^ a = x ^ l ^ γ.shift.val := by
        rw [← pow_mul, mul_comm, pow_mul, hx]
      rw [hfix h hh _ (hroot_mem _ h2)]
      exact h1
    · have hz : (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) ^ l ^ a = (((γ.left : (↥LL.1)ˣ) : ↥LL.1) : Om l) := by
        rw [← hsucc, pow_succ, hζ, one_mul]
      rw [hfix h hh _ (mul_mem (hroot_mem _ hz) (ϖ.pi_mem_field a))]
      exact hg2
  · intro k ζ hk
    obtain ⟨hr, -⟩ := GlobalTheory.T.action_of_covers l a e ϖ LL k _ hk
    have hr' : ∀ x : Om l, x ^ l ^ a = x → k x = x := fun x hx => by
      rw [hr x hx]
      simp
    obtain ⟨k', hk', h, hh, hkh⟩ := GlobalTheory.T.fixing_kunr_mem_inertia_mod_fieldInf l a e ϖ hsucc k hr'
    have hc : Covers ↥LL.1 (thetaW a LL) ϖ (k' : GQ l) (TameGal.inertia ζ : TameGal ↥LL.1 l e a) := by
      have := covers_mul ϖ LL hk (covers_of_mem ϖ LL hh)
      rwa [mul_one, ← hkh] at this
    refine ⟨k', hk', hc, ?_⟩
    rw [(GlobalTheory.T.action_of_covers l a e ϖ LL _ _ hc).2]
    rfl

end GlobalTheory.TameCover
