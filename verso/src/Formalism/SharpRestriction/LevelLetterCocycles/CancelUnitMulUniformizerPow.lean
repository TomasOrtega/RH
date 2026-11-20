import Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfExactnessAndData
import Formalism.SharpRestriction.LevelLetterCocycles.RelayGeneralCaseOfAdmissible
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def GoodZ (T : LocLat G Qp LL O) (c : ZMod n) (j y M σ : ℕ) (Z τ : W.DD T) : Prop :=
  ∃ κ κ' S, SolOK W T c M Z κ S ∧
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M)
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ' • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S))

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem good_iff (T : LocLat G Qp LL O) (c : ZMod n) (j y M σ : ℕ) (w τ : W.DD T) :
    Good W T c j y M σ w τ ↔ GoodZ W T c j y M σ (W.γ T w - w) τ := by
  exact Iff.rfl

/- English proof (translation)
Take `⟨κ, κ', S, hS, hF⟩` from `h`. Use `⟨κ, κ', W.map f S, solOK_map W f hT hT' c M hS, ?_⟩` and prove the remaining obligations. Establish `h2` using `inMultiple_map W f hT hT' c j (Formalism.MainNotions.LiftingTheory.JJ W j y M) hF`. Simplify `h2` using `only [mapA_smul, map_sub, map_φpow]`.
-/
theorem goodZ_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) (j y M σ : ℕ)
    {Z τ : W.DD T} (h : GoodZ W T c j y M σ Z τ) : GoodZ W T' c j y M σ (W.map f Z) (W.map f τ) := by
  obtain ⟨κ, κ', S, hS, hF⟩ := h
  refine ⟨κ, κ', W.map f S, solOK_map W f hT hT' c M hS, ?_⟩
  have h2 := inMultiple_map W f hT hT' c j (Formalism.MainNotions.LiftingTheory.JJ W j y M) hF
  simpa only [mapA_smul, map_sub, map_φpow] using h2

section AlgS

variable {A' M' : Type} [CommRing A'] [AddCommGroup M'] [Module A' M']

/- English proof (translation)
Establish `hG : G = S + L ^ κ • Z + π ^ m • x`. Rewrite using `[← e]`. Normalize the expressions using the abelian group laws. Substitute `hG` using the available equality. Use `module`.
-/
theorem lin_comb1 (L π : A') (σ κ m : ℕ) (G S Z x y : M') (e : G - S - L ^ κ • Z = π ^ m • x) :
    -(L ^ σ • G) - -(L ^ σ • S) - L ^ κ • (π ^ m • y - L ^ σ • Z) =
      π ^ m • (-(L ^ σ • x) - L ^ κ • y) := by
  have hG : G = S + L ^ κ • Z + π ^ m • x := by
    rw [← e]
    abel
  subst hG
  module

/- English proof (translation)
Use `module`.
-/
theorem lin_comb2 (L : A') (a b σ : ℕ) (τ P : M') :
    L ^ a • (L ^ b • -(L ^ σ • τ) - L ^ σ • -(L ^ σ • P)) = -(L ^ σ • (L ^ a • (L ^ b • τ - L ^ σ • P))) := by
  module

end AlgS

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.ArcLiftingSetup.lA, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`.
-/
private theorem lA_pow_smul_eq_p_pow_smul (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x = (PD.p ^ k) • x := by
  simp only [Formalism.MainNotions.ArcLiftingSetup.lA, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Unfold `Formalism.MainNotions.LiftingTheory.InNΔi at hx ⊢`. Conclude with `⟨neg_mem hx.1, neg_mem hx.2⟩`.
-/
theorem InNΔi_neg (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (-x) := by
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at hx ⊢
  exact ⟨neg_mem hx.1, neg_mem hx.2⟩

/- English proof (translation)
Rewrite using `[lA_pow_smul_eq_p_pow_smul]`. Unfold `Formalism.MainNotions.LiftingTheory.InNΔi at hx ⊢`. Conclude with `⟨nsmul_mem hx.1 _, nsmul_mem hx.2 _⟩`.
-/
private theorem InNDeltai_lA_pow_smul_of_InNDeltai (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x) := by
  rw [lA_pow_smul_eq_p_pow_smul]
  unfold Formalism.MainNotions.LiftingTheory.InNΔi at hx ⊢
  exact ⟨nsmul_mem hx.1 _, nsmul_mem hx.2 _⟩

/- English proof (translation)
Unfold `GoodZ SolOK at h ⊢`. Take `⟨κ, κ', S, ⟨⟨S', hS', hSS⟩, x, hx, hxe⟩, hF⟩` from `h`. Establish `hγ : W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S) = Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • W.γ T S`. Rewrite using `[lA_pow_smul_eq_p_pow_smul, map_nsmul, lA_pow_smul_eq_p_pow_smul]`. Establish `hφ : ((W.φD T) ^ j) (-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S)) = -(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S)`.

Rewrite using `[map_neg, lA_pow_smul_eq_p_pow_smul, map_nsmul, lA_pow_smul_eq_p_pow_smul]`. Use `⟨κ, κ', -(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S), ⟨⟨-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S'), InNΔi_neg W T c (InNDeltai_lA_pow_smul_of_InNDeltai W T c σ hS'), ?_⟩, -(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • x) - Formalism.MainNotions.ArcLifting …` and prove the remaining obligations. Rewrite using `[hSS, smul_neg, smul_comm]`. Establish `h1` using `InNDeltai_lA_pow_smul_of_InNDeltai W T c σ hx`. Establish `h2` using `InNDeltai_lA_pow_smul_of_InNDeltai W T c κ hy₀`.

Unfold `Formalism.MainNotions.LiftingTheory.InNΔi at h1 h2 ⊢`. Conclude with `⟨sub_mem (neg_mem h1.1) h2.1, sub_mem (neg_mem h1.2) h2.2⟩`. Rewrite using `[map_neg, hγ, hZ₀]`. Conclude with `lin_comb1 _ _ σ κ M _ _ _ _ _ hxe`. Rewrite using `[hφ, lin_comb2]`.

Take `⟨y', hy', hyx⟩` from `hF`. Use `⟨-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • y'), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lA_pow_smul_eq_p_pow_smul]`. Conclude with `neg_mem (nsmul_mem hy' _)`. Rewrite using `[hyx, smul_neg, smul_comm]`.
-/
theorem goodZ_comb (T : LocLat G Qp LL O) (c : ZMod n) (j y M σ : ℕ) {Z τ Z₀ y₀ : W.DD T}
    (h : GoodZ W T c j y M σ Z τ) (hy₀ : Formalism.MainNotions.LiftingTheory.InNΔi W T c y₀)
    (hZ₀ : Z₀ = W.π₀ ^ M • y₀ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • Z) :
    GoodZ W T c j y M σ Z₀ (-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • τ)) := by
  unfold GoodZ SolOK at h ⊢
  obtain ⟨κ, κ', S, ⟨⟨S', hS', hSS⟩, x, hx, hxe⟩, hF⟩ := h
  have hγ : W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S) = Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • W.γ T S := by
    rw [lA_pow_smul_eq_p_pow_smul, map_nsmul, lA_pow_smul_eq_p_pow_smul]
  have hφ : ((W.φD T) ^ j) (-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S)) =
      -(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S) := by
    rw [map_neg, lA_pow_smul_eq_p_pow_smul, map_nsmul, lA_pow_smul_eq_p_pow_smul]
  refine ⟨κ, κ', -(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S),
    ⟨⟨-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • S'), InNΔi_neg W T c (InNDeltai_lA_pow_smul_of_InNDeltai W T c σ hS'), ?_⟩,
      -(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • x) - Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • y₀, ?_, ?_⟩, ?_⟩
  · rw [hSS, smul_neg, smul_comm]
  · have h1 := InNDeltai_lA_pow_smul_of_InNDeltai W T c σ hx
    have h2 := InNDeltai_lA_pow_smul_of_InNDeltai W T c κ hy₀
    unfold Formalism.MainNotions.LiftingTheory.InNΔi at h1 h2 ⊢
    exact ⟨sub_mem (neg_mem h1.1) h2.1, sub_mem (neg_mem h1.2) h2.2⟩
  · rw [map_neg, hγ, hZ₀]
    exact lin_comb1 _ _ σ κ M _ _ _ _ _ hxe
  · rw [hφ, lin_comb2]
    obtain ⟨y', hy', hyx⟩ := hF
    refine ⟨-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • y'), ?_, ?_⟩
    · rw [lA_pow_smul_eq_p_pow_smul]
      exact neg_mem (nsmul_mem hy' _)
    · rw [hyx, smul_neg, smul_comm]

/- English proof (translation)
Establish `hl : 2 ≤ PD.p` using `PD.hp.two_le`. Establish `hO` using `SatW.p_nzd_O W hC.inj`. Establish `hg : ∀ r m, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p r * cf r m` using `fun r m => int_of_bd W hC.O2 r (h4 r) _ (hbd r m)`. Use `choose g hg using hg`. Establish `hg0 : ∀ m, g 0 m = 0` using `fun m => hC.inj (by rw [hg, hc0]; simp)`.

Establish `hdec : ∀ r, ∃ a'' ∈ W.AΔ, ∃ B ∈ W.AΔ, ∀ m, ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j * ((W.φA ^ A.j) W.π₀) ^ r * algebraMap O (LetA O n) (g r m) = (W.π₀ * a'' * ((PD.p : ℕ) : LetA O n) ^ Ex PD.p r + B * Formalism.MainNotions.LiftingTheory.JJ W …`. Introduce `r`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Conclude with `⟨0, W.AΔ.zero_mem, 0, W.AΔ.zero_mem, fun m => by simp [hg0]⟩`. Take `⟨a, ha, B, hB, h⟩` from `Formalism.MainNotions.LiftingTheory.tr_trunc_int W h9 hp2 A.j (2 * A.G₀) (A.M PD.p) r hj`.

Take `⟨a'', ha'', rfl⟩` from `frobenius_uniformizer_pow_dvd W h9 hO hC.Tr2 A.j (2 * A.G₀) (A.M PD.p) r _ _ hr (M_pos A _) ha h`. Conclude with `⟨a'', ha'', B, hB, fun m => by rw [h]; rfl⟩`. Use `choose a'' ha'' B hB heq using hdec`. Use `set M := A.M PD.p with hMdef`. Use `set κ := Ex PD.p M with hκ`.

Use `set σ := A.σ PD.p with hσ`. Use `set sg := Formalism.NOK.sigNOK PD.p (2 * A.G₀) M A.j with hsg`. Establish `hsgσ : sg ≤ σ` using `sig_le A PD.p`. Set `y : ℕ → Fin d → O` to `fun r m => ((PD.p : ℕ) : O) ^ (κ - Ex PD.p r) * g r m`. Establish `hy : ∀ r < M, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * cf r m`.

Introduce `r hr m`. Establish `hle` using `Ex_mono PD.p hl hr.le`. Simplify using `only [y, map_mul, map_pow, map_natCast, hg]`. Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]`. Establish `hyA : ∀ r m, algebraMap O (LetA O n) (y r m) = Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ - Ex PD.p r) * algebraMap O (LetA O n) (g r m)`.

Introduce `r m`. Simplify using `only [y, map_mul, map_pow, map_natCast]`. Both sides reduce to the same expression. Set `β : Fin d → W.DD T` to `fun m => ((W.φD T) ^ A.j) (b m)`. Establish `hβ : ∀ m, β m ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j` using `fun m => Pp_phi W T c A.j (hb.1 m)`.

Establish `hcoefΔ : ∀ r m, Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a'' r ∈ W.AΔ` using `fun r m => W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) (W.AΔ.algebraMap_mem _)) (ha'' r)`. Set `τ : W.DD T` to `W.π₀ • ∑ r ∈ Finset.range M, ∑ m, (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a'' r) • β m`. Establish `hτ : Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ` using `⟨_, AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ => Pp_smul W T c A.j (hcoefΔ r m) _ (hβ m), rfl⟩`. Establish `hS` using `solOK_of_sol W T hC.inj hC.hπ c b hb _ cf hsol hc0 M (M_pos A _) κ y hy`. Use `set S := ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r) with hSdef`.

Establish `hφS : ((W.φD T) ^ A.j) S = ∑ r ∈ Finset.range M, ∑ m, (((W.φA ^ A.j) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) • β m`. Rewrite using `[hSdef, map_sum]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[φpow_smul, map_pow, Formalism.MainNotions.LiftingTheory.vecB, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, ← algebraMap_smul (LetA O n) (y r m), smul_smul]`. Establish `key : Formalism.MainNotions.ArcLiftingSetup.lA W ^ 0 • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ A.j) S) = Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M • ∑ r ∈ Finset.range M, ∑ m, (-(Formalism. …`. Rewrite using `[hφS, pow_zero, one_smul, smul_smul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, ← sub_smul, smul_smul]`. Use `congr 1`. Establish `hle` using `Ex_mono PD.p hl (Finset.mem_range.1 hr).le`. Use `termId (Formalism.MainNotions.ArcLiftingSetup.lA W) W.π₀ (((W.φA ^ A.j) W.π₀) ^ r) (algebraMap O (LetA O n) (g r m)) (a'' r) (B r) (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M) (σ - sg) sg (κ - Ex PD.p r) (Ex PD.p r) κ σ (by omega) (by omega) (heq r m)` as an intermediate fact.

Rewrite using `[hyA]`. Take the linear combination `this`. Establish `hGood : GoodZ W T c A.j (2 * A.G₀) M σ Z τ`. Use `⟨κ, 0, S, hS, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`.

Use `inMultiple_of_mem W T c A.j _ (AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ => Pp_smul W T c A.j ?_ _ (hβ m))` and prove the remaining obligations. Conclude with `W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) (W.AΔ.pow_mem (lA_mem W) _)) (W.AΔ.algebraMap_mem _)) (hB r))`. Conclude with `⟨τ, hτ, hGood⟩`.
-/
theorem tauZ_exists [IsDomain O] (T : LocLat G Qp LL O) (hC : Ctx W T) (h9 : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W)
    (hp2 : PD.p ≠ 2) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hj : 1 ≤ A.j) (c : ZMod n) (Z : W.DD T)
    {d : ℕ} (b : Fin d → W.DD T) (cf : ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b)
    (hsol : Formalism.MainNotions.LiftingTheory.IsSol W T c b Z cf) (hc0 : cf 0 = 0)
    (hbd : ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (cf r m))
    (h4 : ∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1)) :
    ∃ τ, Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ ∧
      GoodZ W T c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) Z τ := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hO := SatW.p_nzd_O W hC.inj
  have hg : ∀ r m, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p r * cf r m :=
    fun r m => int_of_bd W hC.O2 r (h4 r) _ (hbd r m)
  choose g hg using hg
  have hg0 : ∀ m, g 0 m = 0 := fun m => hC.inj (by rw [hg, hc0]; simp)
  have hdec : ∀ r, ∃ a'' ∈ W.AΔ, ∃ B ∈ W.AΔ, ∀ m,
      ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j *
          ((W.φA ^ A.j) W.π₀) ^ r * algebraMap O (LetA O n) (g r m) =
        (W.π₀ * a'' * ((PD.p : ℕ) : LetA O n) ^ Ex PD.p r +
          B * Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p)) * algebraMap O (LetA O n) (g r m) := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨0, W.AΔ.zero_mem, 0, W.AΔ.zero_mem, fun m => by simp [hg0]⟩
    · obtain ⟨a, ha, B, hB, h⟩ := Formalism.MainNotions.LiftingTheory.tr_trunc_int W h9 hp2 A.j (2 * A.G₀) (A.M PD.p) r hj
      obtain ⟨a'', ha'', rfl⟩ := frobenius_uniformizer_pow_dvd W h9 hO hC.Tr2 A.j (2 * A.G₀) (A.M PD.p) r _ _ hr
        (M_pos A _) ha h
      exact ⟨a'', ha'', B, hB, fun m => by rw [h]; rfl⟩
  choose a'' ha'' B hB heq using hdec
  set M := A.M PD.p with hMdef
  set κ := Ex PD.p M with hκ
  set σ := A.σ PD.p with hσ
  set sg := Formalism.NOK.sigNOK PD.p (2 * A.G₀) M A.j with hsg
  have hsgσ : sg ≤ σ := sig_le A PD.p
  let y : ℕ → Fin d → O := fun r m => ((PD.p : ℕ) : O) ^ (κ - Ex PD.p r) * g r m
  have hy : ∀ r < M, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * cf r m := by
    intro r hr m
    have hle := Ex_mono PD.p hl hr.le
    simp only [y, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hyA : ∀ r m, algebraMap O (LetA O n) (y r m) =
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ - Ex PD.p r) * algebraMap O (LetA O n) (g r m) := by
    intro r m; simp only [y, map_mul, map_pow, map_natCast]; rfl
  let β : Fin d → W.DD T := fun m => ((W.φD T) ^ A.j) (b m)
  have hβ : ∀ m, β m ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j := fun m => Pp_phi W T c A.j (hb.1 m)
  have hcoefΔ : ∀ r m, Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a'' r ∈ W.AΔ :=
    fun r m => W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) (W.AΔ.algebraMap_mem _)) (ha'' r)
  let τ : W.DD T := W.π₀ • ∑ r ∈ Finset.range M, ∑ m,
    (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a'' r) • β m
  have hτ : Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ :=
    ⟨_, AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Pp_smul W T c A.j (hcoefΔ r m) _ (hβ m), rfl⟩
  have hS := solOK_of_sol W T hC.inj hC.hπ c b hb _ cf hsol hc0 M (M_pos A _) κ y hy
  set S := ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r) with hSdef
  have hφS : ((W.φD T) ^ A.j) S = ∑ r ∈ Finset.range M, ∑ m,
      (((W.φA ^ A.j) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) • β m := by
    rw [hSdef, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [φpow_smul, map_pow, Formalism.MainNotions.LiftingTheory.vecB, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, ← algebraMap_smul (LetA O n) (y r m), smul_smul]
  have key : Formalism.MainNotions.ArcLiftingSetup.lA W ^ 0 • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ A.j) S) =
      Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M • ∑ r ∈ Finset.range M, ∑ m,
        (-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ - Ex PD.p r) *
          algebraMap O (LetA O n) (g r m) * B r)) • β m := by
    rw [hφS, pow_zero, one_smul, smul_smul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, smul_smul, ← sub_smul, smul_smul]
    congr 1
    have hle := Ex_mono PD.p hl (Finset.mem_range.1 hr).le
    have := termId (Formalism.MainNotions.ArcLiftingSetup.lA W) W.π₀ (((W.φA ^ A.j) W.π₀) ^ r)
      (algebraMap O (LetA O n) (g r m)) (a'' r) (B r) (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M)
      (σ - sg) sg (κ - Ex PD.p r) (Ex PD.p r) κ σ (by omega) (by omega) (heq r m)
    rw [hyA]
    linear_combination this
  have hGood : GoodZ W T c A.j (2 * A.G₀) M σ Z τ := by
    refine ⟨κ, 0, S, hS, ?_⟩
    rw [key]
    refine inMultiple_of_mem W T c A.j _ (AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Pp_smul W T c A.j ?_ _ (hβ m))
    exact W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _)
      (W.AΔ.pow_mem (lA_mem W) _)) (W.AΔ.algebraMap_mem _)) (hB r))
  exact ⟨τ, hτ, hGood⟩

end Formalism.MainNotions.UnusedSlot80.Relay2

namespace Formalism.MainNotions.UnusedSlot80.Split2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

/- English proof (translation)
Rewrite `hg`, `hh`, the goal using `[W.DelF_def]`. Take `⟨a, ha, hga⟩` from `hg`. Take `⟨b, hb, hhb⟩` from `hh`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, hga, one_pow, mul_comm a b, pow_mul, hhb, one_pow, one_mul]`.
-/
theorem DelF_mul {g h : W.Gam} (hg : g ∈ W.DelF) (hh : h ∈ W.DelF) : g * h ∈ W.DelF := by
  rw [W.DelF_def] at hg hh ⊢
  obtain ⟨a, ha, hga⟩ := hg
  obtain ⟨b, hb, hhb⟩ := hh
  refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
  rw [mul_pow, pow_mul, hga, one_pow, mul_comm a b, pow_mul, hhb, one_pow, one_mul]

/- English proof (translation)
Rewrite `hg`, the goal using `[W.DelF_def]`. Take `⟨k, hk, hgk⟩` from `hg`. Conclude with `⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩`.
-/
theorem DelF_inv {g : W.Gam} (hg : g ∈ W.DelF) : g⁻¹ ∈ W.DelF := by
  rw [W.DelF_def] at hg ⊢
  obtain ⟨k, hk, hgk⟩ := hg
  exact ⟨k, hk, by rw [inv_pow, hgk, inv_one]⟩

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[map_sum]`. Repeatedly rewrite using `[← W.γD_mul]`. Conclude with `Finset.sum_nbij' (fun g => δ * g) (fun g => δ⁻¹ * g) (fun a ha => DelF_mul W hδ ha) (fun a ha => DelF_mul W (DelF_inv W hδ) ha) (fun a _ => inv_mul_cancel_left δ a) (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)`.
-/
theorem sumΔ_inv (T : LocLat G Qp LL O) (x : W.DD T) :
    ∀ δ ∈ W.DelF, W.γD T δ (∑ g ∈ W.DelF, W.γD T g x) = ∑ g ∈ W.DelF, W.γD T g x := by
  intro δ hδ
  rw [map_sum]
  simp_rw [← W.γD_mul]
  exact Finset.sum_nbij' (fun g => δ * g) (fun g => δ⁻¹ * g) (fun a ha => DelF_mul W hδ ha)
    (fun a ha => DelF_mul W (DelF_inv W hδ) ha) (fun a _ => inv_mul_cancel_left δ a)
    (fun a _ => mul_inv_cancel_left δ a) (fun a _ => rfl)

/- English proof (translation)
Take `⟨w, hw⟩` from `hw`. Rewrite using `[hw, map_mul, map_pow]`. Conclude with `(w.isUnit.map _).mul (W.EE_π.pow _)`.
-/
theorem uniformizer_isUnit_etale (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) :
    IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  obtain ⟨w, hw⟩ := hw
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

/- English proof (translation)
Establish `h2 : (algebraMap (LetA O n) W.EE W.π₀ ^ k) • x = 0`. Rewrite using `[← map_pow, algebraMap_smul]`. Conclude with `h`. Conclude with `((hu.pow k).smul_eq_zero).mp h2`.
-/
theorem cancel_unit_mul_uniformizer_pow (hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀)) (T : LocLat G Qp LL O) (k : ℕ)
    {x : W.DD T} (h : W.π₀ ^ k • x = 0) : x = 0 := by
  have h2 : (algebraMap (LetA O n) W.EE W.π₀ ^ k) • x = 0 := by
    rw [← map_pow, algebraMap_smul]
    exact h
  exact ((hu.pow k).smul_eq_zero).mp h2

/- English proof (translation)
Use `⟨hY, fun i τ hτ a ha => ?_⟩` and prove the remaining obligations. Break down `(hJ T₂ Y W.one ι π hses hT.1 hY hone.1 τ a).1 ha with h | h` into its components or cases. Conclude with `hT.2 i τ hτ a h`. Rewrite using `[hone.2 τ a h]`. Apply the tactic sequence `cases A.ty i <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.win]`.
-/
theorem win_ext (A : ArcP n) {T₂ Y : LocLat G Qp LL O} {ι : LatHom T₂.L Y.L} {π : LatHom Y.L W.one.L}
    (hJ : Formalism.MainNotions.LiftingTheory.coreJumps PD LL O)
    (hone : IsCrys PD W.one.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD W.one.ρ τ a → a = 0)
    (hT : Win W A T₂) (hY : IsCrys PD Y.ρ) (hses : IsSESLat (Qp := Qp) ι π) : Win W A Y := by
  refine ⟨hY, fun i τ hτ a ha => ?_⟩
  rcases (hJ T₂ Y W.one ι π hses hT.1 hY hone.1 τ a).1 ha with h | h
  · exact hT.2 i τ hτ a h
  · rw [hone.2 τ a h]
    cases A.ty i <;> simp [Formalism.MainNotions.LocalTheoryWindows.LT.win]

/- English proof (translation)
Use `module`.
-/
theorem lin3 {A' M' : Type} [CommRing A'] [AddCommGroup M'] [Module A' M'] (π L : A') (k σ : ℕ)
    (y u : M') : π ^ (k + 1) • y - L ^ σ • (π • u) = π • (π ^ k • y - L ^ σ • u) := by
  module

/- English proof (translation)
Rewrite using `[← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]`. Use `congr 1`. Unfold `letγ letE`. Use function extensionality and compare the values at `i`. Simplify using `only [AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]`.

Break down `eq_or_ne i c with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
private theorem gammaD_letE_smul_comm (T : LocLat G Qp LL O) (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, algebraMap_smul]
  congr 1
  unfold letγ letE
  funext i
  simp only [AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply]
  rcases eq_or_ne i c with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Conclude with `gammaD_letE_smul_comm W T W.gam c x`.
-/
theorem γ_letE (T : LocLat G Qp LL O) (c : ZMod n) (x : W.DD T) :
    W.γ T ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γ T x := by
  exact gammaD_letE_smul_comm W T W.gam c x

/- English proof (translation)
Conclude with `gammaD_letE_smul_comm W T g c x`.
-/
theorem γD_letE (T : LocLat G Qp LL O) (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  exact gammaD_letE_smul_comm W T g c x

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.ArcLiftingSetup.lA, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]`.
-/
theorem γD_lA (T : LocLat G Qp LL O) (g : W.Gam) (k : ℕ) (x : W.DD T) :
    W.γD T g (lA W ^ k • x) = lA W ^ k • W.γD T g x := by
  simp only [Formalism.MainNotions.ArcLiftingSetup.lA, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, map_nsmul]

/- English proof (translation)
Unfold `Formalism.BasicNotions.LocWach.Nl at hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]`. Use `congr 1`. Unfold `letE`.

Rewrite using `[← Pi.single_mul, one_mul]`.
-/
theorem letE_of_Nl {T : LocLat G Qp LL O} {c : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T c) :
    (letE c : LetA O n) • x = x := by
  unfold Formalism.BasicNotions.LocWach.Nl at hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  congr 1
  unfold letE
  rw [← Pi.single_mul, one_mul]

/- English proof (translation)
Unfold `Formalism.BasicNotions.LocWach.Nl at hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem N_of_Nl {T : LocLat G Qp LL O} {c : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T c) : x ∈ W.N T := by
  unfold Formalism.BasicNotions.LocWach.Nl at hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Conclude with `Formalism.MainNotions.LiftingTheory.gammaD_mem_letter W T g c x hx`.
-/
theorem γD_Nl {T : LocLat G Qp LL O} {c : ZMod n} (g : W.Gam) {x : W.DD T} (hx : x ∈ W.Nl T c) :
    W.γD T g x ∈ W.Nl T c := by
  exact Formalism.MainNotions.LiftingTheory.gammaD_mem_letter W T g c x hx

/- English proof (translation)
Take `⟨e₁, he₁, hT⟩` from `W.one_line`. Establish `hmem : e₁ ∈ W.one.L.T` using `by rw [hT]; exact Submodule.mem_span_singleton_self e₁`. Set `f : O →ₗ[O] ↥W.one.L.T` to `LinearMap.toSpanSingleton O _ ⟨e₁, hmem⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion.

Introduce `a b hab`. Establish `h1 : (a - b) • e₁ = 0`. Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul] at this`. Rewrite using `[sub_smul, this, sub_self]`.

Rewrite `h1` using `[← algebraMap_smul LL (a - b) e₁]`. Break down `smul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 (hinj (by rw [h, map_zero]))`. Conclude with `absurd h he₁`. Introduce and unpack `⟨z, hz⟩`.

Establish `hz'` using `hz`. Rewrite `hz'` using `[hT, Submodule.mem_span_singleton]`. Take `⟨a, ha⟩` from `hz'`. Conclude with `⟨a, Subtype.ext (by simp [f, ha])⟩`. Rewrite using `[← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_self]`.
-/
theorem finrank_one_lat [IsDomain O] (hinj : Function.Injective (algebraMap O LL)) :
    Module.finrank O ↥W.one.L.T = 1 := by
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have hmem : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  let f : O →ₗ[O] ↥W.one.L.T := LinearMap.toSpanSingleton O _ ⟨e₁, hmem⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h1 : (a - b) • e₁ = 0 := by
        have := congrArg Subtype.val hab
        simp only [f, LinearMap.toSpanSingleton_apply, Submodule.coe_smul] at this
        rw [sub_smul, this, sub_self]
      rw [← algebraMap_smul LL (a - b) e₁] at h1
      rcases smul_eq_zero.1 h1 with h | h
      · exact sub_eq_zero.1 (hinj (by rw [h, map_zero]))
      · exact absurd h he₁
    · rintro ⟨z, hz⟩
      have hz' := hz
      rw [hT, Submodule.mem_span_singleton] at hz'
      obtain ⟨a, ha⟩ := hz'
      exact ⟨a, Subtype.ext (by simp [f, ha])⟩
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_self]

/- English proof (translation)
Establish `hb` using `W.N_base W.one hone`. Establish `hspan : ∀ z : W.DD W.one, ∃ ζ : W.EE, z = ζ • e`. Introduce `z`. Take `⟨t, rfl⟩` from `hb.equiv.surjective z`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul s m`. Take `⟨m, hm⟩` from `m`. Establish `hm'` using `hm`. Rewrite `hm'` using `[heSpan, Submodule.mem_span_singleton]`.

Take `⟨a', ha'⟩` from `hm'`. Use `⟨s * algebraMap (LetA O n) W.EE a', ?_⟩` and prove the remaining obligations. Rewrite using `[hb.equiv_tmul, mul_smul, algebraMap_smul]`. Simplify using `[ha']`. Consider the case `add t₁ t₂ h₁ h₂`.

Take `⟨ζ₁, h₁⟩` from `h₁`. Take `⟨ζ₂, h₂⟩` from `h₂`. Conclude with `⟨ζ₁ + ζ₂, by rw [map_add, h₁, h₂, add_smul]⟩`. Use `haveI : Nontrivial W.EE := W.EE_inj.nontrivial`. Take `⟨hfree, hrank⟩` from `W.DD_free W.one`.

Rewrite `hrank` using `[finrank_one_lat W hinj]`. Use `haveI := hfree`. Use `haveI : Module.Finite W.EE (W.DD W.one) := Module.finite_of_finrank_pos (by omega)`. Set `bs` to `Module.Free.chooseBasis W.EE (W.DD W.one)`. Establish `hcard : 0 < Fintype.card (Module.Free.ChooseBasisIndex W.EE (W.DD W.one))`.

Rewrite using `[← Module.finrank_eq_card_chooseBasisIndex]`. Use linear arithmetic over natural numbers and integers. Take `⟨i⟩` from `Fintype.card_pos_iff.1 hcard`. Establish `h0 : algebraMap (LetA O n) W.EE a • bs i = 0`. Take `⟨ζ, hζ⟩` from `hspan (bs i)`.

Rewrite using `[hζ, smul_comm, algebraMap_smul, h, smul_zero]`. Establish `h1 : algebraMap (LetA O n) W.EE a = 0` using `(linearIndependent_iff'.1 bs.linearIndependent) {i} (fun _ => algebraMap (LetA O n) W.EE a) (by rw [Finset.sum_singleton]; exact h0) i (Finset.mem_singleton_self i)`. Conclude with `W.EE_inj (by rw [h1, map_zero])`.
-/
theorem e_tf [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hone : IsCrys PD W.one.ρ) {e : W.DD W.one}
    (heSpan : W.N W.one = Submodule.span (LetA O n) {e}) (a : LetA O n) (h : a • e = 0) : a = 0 := by
  have hb := W.N_base W.one hone
  have hspan : ∀ z : W.DD W.one, ∃ ζ : W.EE, z = ζ • e := by
    intro z
    obtain ⟨t, rfl⟩ := hb.equiv.surjective z
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul s m =>
      obtain ⟨m, hm⟩ := m
      have hm' := hm
      rw [heSpan, Submodule.mem_span_singleton] at hm'
      obtain ⟨a', ha'⟩ := hm'
      refine ⟨s * algebraMap (LetA O n) W.EE a', ?_⟩
      rw [hb.equiv_tmul, mul_smul, algebraMap_smul]
      simp [ha']
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨ζ₁, h₁⟩ := h₁
      obtain ⟨ζ₂, h₂⟩ := h₂
      exact ⟨ζ₁ + ζ₂, by rw [map_add, h₁, h₂, add_smul]⟩
  haveI : Nontrivial W.EE := W.EE_inj.nontrivial
  obtain ⟨hfree, hrank⟩ := W.DD_free W.one
  rw [finrank_one_lat W hinj] at hrank
  haveI := hfree
  haveI : Module.Finite W.EE (W.DD W.one) := Module.finite_of_finrank_pos (by omega)
  let bs := Module.Free.chooseBasis W.EE (W.DD W.one)
  have hcard : 0 < Fintype.card (Module.Free.ChooseBasisIndex W.EE (W.DD W.one)) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex]; omega
  obtain ⟨i⟩ := Fintype.card_pos_iff.1 hcard
  have h0 : algebraMap (LetA O n) W.EE a • bs i = 0 := by
    obtain ⟨ζ, hζ⟩ := hspan (bs i)
    rw [hζ, smul_comm, algebraMap_smul, h, smul_zero]
  have h1 : algebraMap (LetA O n) W.EE a = 0 :=
    (linearIndependent_iff'.1 bs.linearIndependent) {i} (fun _ => algebraMap (LetA O n) W.EE a)
      (by rw [Finset.sum_singleton]; exact h0) i (Finset.mem_singleton_self i)
  exact W.EE_inj (by rw [h1, map_zero])

/- English proof (translation)
Use `set s : W.DD Y := ∑ g ∈ W.DelF, W.γD Y g z with hs`. Use `set y : W.DD Y := ((hΔu.unit⁻¹ : Oˣ) : O) • s with hy`. Establish `hsNl : s ∈ W.Nl Y c` using `Submodule.sum_mem _ fun g _ => γD_Nl W g hz`. Establish `hyNl : y ∈ W.Nl Y c` using `(W.Nl Y c).smul_of_tower_mem _ hsNl`. Establish `hyΔ : ∀ δ ∈ W.DelF, W.γD Y δ y = y` using `fun δ hδ => by`.

Rewrite using `[hy, map_smul, sumΔ_inv W Y z δ hδ]`. Use `⟨y, ⟨⟨N_of_Nl W hyNl, hyΔ⟩, hyNl⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ g ∈ W.DelF, W.map π (W.γD Y g z) = t` using `fun g hg => by rw [W.map_γ, ht, htΔ g hg]`. Rewrite using `[hy, LinearMap.map_smul_of_tower, hs, map_sum, Finset.sum_congr rfl h1, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, smul_smul, hΔu.val_inv_mul, one_smul]`.
-/
theorem lift_avg (hΔu : IsUnit ((W.DelF.card : ℕ) : O)) {Y : LocLat G Qp LL O}
    (π : LatHom Y.L W.one.L) (c : ZMod n) {z : W.DD Y} (hz : z ∈ W.Nl Y c) {t : W.DD W.one}
    (ht : W.map π z = t) (htΔ : ∀ δ ∈ W.DelF, W.γD W.one δ t = t) :
    ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W Y c y ∧ W.map π y = t := by
  set s : W.DD Y := ∑ g ∈ W.DelF, W.γD Y g z with hs
  set y : W.DD Y := ((hΔu.unit⁻¹ : Oˣ) : O) • s with hy
  have hsNl : s ∈ W.Nl Y c := Submodule.sum_mem _ fun g _ => γD_Nl W g hz
  have hyNl : y ∈ W.Nl Y c := (W.Nl Y c).smul_of_tower_mem _ hsNl
  have hyΔ : ∀ δ ∈ W.DelF, W.γD Y δ y = y := fun δ hδ => by
    rw [hy, map_smul, sumΔ_inv W Y z δ hδ]
  refine ⟨y, ⟨⟨N_of_Nl W hyNl, hyΔ⟩, hyNl⟩, ?_⟩
  have h1 : ∀ g ∈ W.DelF, W.map π (W.γD Y g z) = t := fun g hg => by rw [W.map_γ, ht, htΔ g hg]
  rw [hy, LinearMap.map_smul_of_tower, hs, map_sum, Finset.sum_congr rfl h1, Finset.sum_const,
    ← Nat.cast_smul_eq_nsmul O, smul_smul, hΔu.val_inv_mul, one_smul]

/- English proof (translation)
Establish `inj : ∀ x x' : W.DD T₂, W.map ι x = W.map ι x' → x = x'` using `fun x x' h => sub_eq_zero.1 (hinjι _ (by rw [map_sub, h, sub_self]))`. Establish `htf` using `e_tf W hinj hone heSpan`. Establish `hφe : ((W.φD W.one) ^ e') ((letE c : LetA O n) • e) = (letE (c + (e' : ZMod n)) : LetA O n) • e` using `Split.φ_letE_e W e heφ c e'`. Establish `key : ∀ u ∈ Pp W Y c e', ∃ (θ : LetA O n), ∃ v ∈ Pp W T₂ c e', W.map π u = θ • ((letE (c + (e' : ZMod n)) : LetA O n) • e) ∧ (W.φA ^ e') g • u - θ • ((W.φD Y) ^ e') y = W.map ι v`. Use `Relay2.Pp_ind W Y c e' _ ⟨0, 0, (Pp W T₂ c e').zero_mem, by simp, by simp⟩ ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `u₁ u₂ ⟨θ₁, v₁, hv₁, h₁, e₁⟩ ⟨θ₂, v₂, hv₂, h₂, e₂⟩`. Use `⟨θ₁ + θ₂, v₁ + v₂, (Pp W T₂ c e').add_mem hv₁ hv₂, by rw [map_add, h₁, h₂, add_smul], ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← e₁, ← e₂, smul_add, add_smul]`. Normalize the expressions using the abelian group laws. Introduce and unpack `u ⟨θ, v, hv, h, e₁⟩`.

Use `⟨-θ, -v, (Pp W T₂ c e').neg_mem hv, by rw [map_neg, h, neg_smul], ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, ← e₁, smul_neg, neg_smul]`. Normalize the expressions using the abelian group laws. Introduce `a ha z hz`. Establish `hzN : W.map π z ∈ W.N W.one` using `W.map_N π hYc hone z hz.1.1`.

Rewrite `hzN` using `[heSpan, Submodule.mem_span_singleton]`. Take `⟨h₀, hh₀⟩` from `hzN`. Establish `hzc : (letE c : LetA O n) • z = z` using `Relay2.InNΔi_letter W Y c hz`. Establish `hπz : W.map π z = h₀ • ((letE c : LetA O n) • e)`. Rewrite using `[← hzc, Relay2.mapA_smul, ← hh₀, smul_comm]`.

Establish `hh₀Δ : h₀ ∈ W.AΔ` using `fun δ hδ => by`. Establish `e1 : (W.γA δ h₀ - h₀) • e = 0`. Rewrite using `[sub_smul, ← heγ δ, ← γD_smulA, heγ δ, hh₀, ← W.map_γ, hz.1.2 δ hδ, sub_self]`. Conclude with `sub_eq_zero.1 (htf _ e1)`. Establish `hnπ : W.map π (W.π₀ ^ 0 • (g • z - h₀ • y)) = 0`.

Rewrite using `[pow_zero, one_smul, map_sub, Relay2.mapA_smul, Relay2.mapA_smul, hπz, hyπ, smul_comm g h₀, sub_self]`. Establish `hnNΔ : g • z - h₀ • y ∈ W.NΔ Y` using `(W.NΔ Y).sub_mem (PhiPowers.smul_mem_NΔ W Y hg hz.1) (PhiPowers.smul_mem_NΔ W Y hh₀Δ hy.1)`. Establish `hnc : (letE c : LetA O n) • (g • z - h₀ • y) = g • z - h₀ • y`. Rewrite using `[smul_sub, smul_comm _ g, smul_comm _ h₀, hzc, Relay2.InNΔi_letter W Y c hy]`. Rewrite `hnπ` using `[pow_zero, one_smul]`.

Take `⟨m, hm⟩` from `hmid _ hnπ`. Establish `hmN : m ∈ W.N T₂` using `h6d m (by rw [hm]; exact hnNΔ.1)`. Establish `hmi : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c m` using `Relay2.InNΔi_of W T₂ c ⟨hmN, fun δ hδ => inj _ _ (by rw [W.map_γ, hm, hnNΔ.2 δ hδ])⟩ (inj _ _ (by rw [Relay2.mapA_smul, hm, hnc]))`. Use `⟨a * (W.φA ^ e') h₀, a • ((W.φD T₂) ^ e') m, Relay2.Pp_gen W T₂ c e' ha hmi, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Relay2.mapA_smul, Relay2.map_φpow, hπz, Split.φpow_smulA, hφe, smul_smul, smul_smul]`.

Rewrite using `[Relay2.mapA_smul, Relay2.map_φpow, hm, map_sub, Split.φpow_smulA, Split.φpow_smulA, smul_sub, smul_comm _ a, ← mul_smul, mul_comm]`. Simplify using `only [mul_smul]`. Take `⟨θ, v, hv, h₁, h₂⟩` from `key _ hx`. Rewrite `h₁` using `[hπι, smul_smul]`. Establish `hθ : θ * letE (c + (e' : ZMod n)) = 0` using `htf _ h₁.symm`.

Establish `hyl : (letE (c + (e' : ZMod n)) : LetA O n) • ((W.φD Y) ^ e') y = ((W.φD Y) ^ e') y` using `PhiPowers.φD_pow_letter W Y c y (Relay2.InNΔi_letter W Y c hy) e'`. Rewrite `h₂` using `[← hyl, smul_smul, hθ, zero_smul, sub_zero]`. Establish `hxv : (W.φA ^ e') g • x = v` using `inj _ _ (by rw [Relay2.mapA_smul]; exact h₂)`. Rewrite using `[hxv]`. Conclude with `hv`.
-/
theorem pp_pull [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hone : IsCrys PD W.one.ρ) {T₂ Y : LocLat G Qp LL O} {ι : LatHom T₂.L Y.L}
    {π : LatHom Y.L W.one.L} (hYc : IsCrys PD Y.ρ) (hmid : ∀ u, W.map π u = 0 → ∃ x, W.map ι x = u)
    (hinjι : ∀ x, W.map ι x = 0 → x = 0) (hπι : ∀ x, W.map π (W.map ι x) = 0)
    (h6d : ∀ x : W.DD T₂, W.map ι x ∈ W.N Y → x ∈ W.N T₂) {e : W.DD W.one}
    (heSpan : W.N W.one = Submodule.span (LetA O n) {e}) (heφ : W.φD W.one e = e)
    (heγ : ∀ g, W.γD W.one g e = e) (c : ZMod n) {g : LetA O n} (hg : g ∈ W.AΔ) {y : W.DD Y}
    (hy : Formalism.MainNotions.LiftingTheory.InNΔi W Y c y) (hyπ : W.map π y = g • ((letE c : LetA O n) • e)) (e' : ℕ)
    (x : W.DD T₂) (hx : W.map ι x ∈ Pp W Y c e') : (W.φA ^ e') g • x ∈ Pp W T₂ c e' := by
  have inj : ∀ x x' : W.DD T₂, W.map ι x = W.map ι x' → x = x' := fun x x' h =>
    sub_eq_zero.1 (hinjι _ (by rw [map_sub, h, sub_self]))
  have htf := e_tf W hinj hone heSpan
  have hφe : ((W.φD W.one) ^ e') ((letE c : LetA O n) • e) = (letE (c + (e' : ZMod n)) : LetA O n) • e :=
    Split.φ_letE_e W e heφ c e'
  have key : ∀ u ∈ Pp W Y c e', ∃ (θ : LetA O n), ∃ v ∈ Pp W T₂ c e',
      W.map π u = θ • ((letE (c + (e' : ZMod n)) : LetA O n) • e) ∧
      (W.φA ^ e') g • u - θ • ((W.φD Y) ^ e') y = W.map ι v := by
    refine Relay2.Pp_ind W Y c e' _ ⟨0, 0, (Pp W T₂ c e').zero_mem, by simp, by simp⟩ ?_ ?_ ?_
    · rintro u₁ u₂ ⟨θ₁, v₁, hv₁, h₁, e₁⟩ ⟨θ₂, v₂, hv₂, h₂, e₂⟩
      refine ⟨θ₁ + θ₂, v₁ + v₂, (Pp W T₂ c e').add_mem hv₁ hv₂, by rw [map_add, h₁, h₂, add_smul], ?_⟩
      rw [map_add, ← e₁, ← e₂, smul_add, add_smul]
      abel
    · rintro u ⟨θ, v, hv, h, e₁⟩
      refine ⟨-θ, -v, (Pp W T₂ c e').neg_mem hv, by rw [map_neg, h, neg_smul], ?_⟩
      rw [map_neg, ← e₁, smul_neg, neg_smul]
      abel
    · intro a ha z hz

      have hzN : W.map π z ∈ W.N W.one := W.map_N π hYc hone z hz.1.1
      rw [heSpan, Submodule.mem_span_singleton] at hzN
      obtain ⟨h₀, hh₀⟩ := hzN
      have hzc : (letE c : LetA O n) • z = z := Relay2.InNΔi_letter W Y c hz
      have hπz : W.map π z = h₀ • ((letE c : LetA O n) • e) := by
        rw [← hzc, Relay2.mapA_smul, ← hh₀, smul_comm]
      have hh₀Δ : h₀ ∈ W.AΔ := fun δ hδ => by
        have e1 : (W.γA δ h₀ - h₀) • e = 0 := by
          rw [sub_smul, ← heγ δ, ← γD_smulA, heγ δ, hh₀, ← W.map_γ, hz.1.2 δ hδ, sub_self]
        exact sub_eq_zero.1 (htf _ e1)

      have hnπ : W.map π (W.π₀ ^ 0 • (g • z - h₀ • y)) = 0 := by
        rw [pow_zero, one_smul, map_sub, Relay2.mapA_smul, Relay2.mapA_smul, hπz, hyπ, smul_comm g h₀,
          sub_self]
      have hnNΔ : g • z - h₀ • y ∈ W.NΔ Y :=
        (W.NΔ Y).sub_mem (PhiPowers.smul_mem_NΔ W Y hg hz.1) (PhiPowers.smul_mem_NΔ W Y hh₀Δ hy.1)
      have hnc : (letE c : LetA O n) • (g • z - h₀ • y) = g • z - h₀ • y := by
        rw [smul_sub, smul_comm _ g, smul_comm _ h₀, hzc, Relay2.InNΔi_letter W Y c hy]
      rw [pow_zero, one_smul] at hnπ
      obtain ⟨m, hm⟩ := hmid _ hnπ
      have hmN : m ∈ W.N T₂ := h6d m (by rw [hm]; exact hnNΔ.1)
      have hmi : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c m := Relay2.InNΔi_of W T₂ c
        ⟨hmN, fun δ hδ => inj _ _ (by rw [W.map_γ, hm, hnNΔ.2 δ hδ])⟩ (inj _ _ (by rw [Relay2.mapA_smul, hm, hnc]))
      refine ⟨a * (W.φA ^ e') h₀, a • ((W.φD T₂) ^ e') m, Relay2.Pp_gen W T₂ c e' ha hmi, ?_, ?_⟩
      · rw [Relay2.mapA_smul, Relay2.map_φpow, hπz, Split.φpow_smulA, hφe, smul_smul, smul_smul]
      · rw [Relay2.mapA_smul, Relay2.map_φpow, hm, map_sub, Split.φpow_smulA, Split.φpow_smulA,
          smul_sub, smul_comm _ a, ← mul_smul, mul_comm]
        simp only [mul_smul]
  obtain ⟨θ, v, hv, h₁, h₂⟩ := key _ hx
  rw [hπι, smul_smul] at h₁
  have hθ : θ * letE (c + (e' : ZMod n)) = 0 := htf _ h₁.symm
  have hyl : (letE (c + (e' : ZMod n)) : LetA O n) • ((W.φD Y) ^ e') y = ((W.φD Y) ^ e') y :=
    PhiPowers.φD_pow_letter W Y c y (Relay2.InNΔi_letter W Y c hy) e'
  rw [← hyl, smul_smul, hθ, zero_smul, sub_zero] at h₂
  have hxv : (W.φA ^ e') g • x = v := inj _ _ (by rw [Relay2.mapA_smul]; exact h₂)
  rw [hxv]
  exact hv

/- English proof (translation)
Introduce `hCA h5 A hA T₂ Y ι π hT₂ hY hses rr hK e heN heSpan heφ heγ b`. Establish `hT₂c : IsCrys PD T₂.ρ` using `hT₂.1`. Establish `hl : 2 ≤ PD.p` using `PD.hp.two_le`. Take `⟨hπι, hinjι, hmid⟩` from `hEx T₂ Y ι π hT₂c hY hses`. Establish `inj : ∀ x x' : W.DD T₂, W.map ι x = W.map ι x' → x = x'` using `fun x x' h => sub_eq_zero.1 (hinjι _ (by rw [map_sub, h, sub_self]))`.

Establish `h6d : ∀ x : W.DD T₂, W.map ι x ∈ W.N Y → x ∈ W.N T₂` using `(h6.2.2 T₂ Y W.one ι π hT₂c hY hone.1 hses).2.2.2.1`. Establish `hR9Y` using `Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA Y hY`. Establish `hR9` using `Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA T₂ hT₂c`. Establish `hu` using `uniformizer_isUnit_etale W hR9Y.1.2.2.1`. Establish `hπ : W.π₀ ∈ W.AΔ` using `hR9Y.1.1`.

Establish `hWY : Win W A Y` using `win_ext W A hJ hone hT₂ hY hses`. Establish `hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p` using `Relay2.arith_M PD.p A.G₀ A.h hl hA.2.2.2.2.2.1`. Establish `hlt : A.h < (PD.p - 1) * A.M PD.p` using `Split.arith_h PD.p A.h hl`. Establish `hJ2` using `Split.jumpsLe_of_win W A hA T₂ hT₂`. Establish `hF1a` using `((hF1 hCA A.h (A.M PD.p) hlt).1 T₂ hT₂c hJ2).1`.

Establish `hq : qA W ∈ W.AΔ` using `W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)`. Establish `hγι : ∀ z : W.DD T₂, W.map ι (W.γ T₂ z) = W.γ Y (W.map ι z)` using `fun z => W.map_γ ι W.gam z`. Establish `hγπ : ∀ z : W.DD Y, W.map π (W.γ Y z) = W.γ W.one (W.map π z)` using `fun z => W.map_γ π W.gam z`. Establish `hCY` using `Relay2.ctx_of W hinj hO2 h9 hH hTr hCA Y hY`. Establish `hC` using `Relay2.ctx_of W hinj hO2 h9 hH hTr hCA T₂ hT₂c`.

Establish `pull : ∀ (k : ℕ) (y : W.DD Y) (i : ZMod n), y ∈ W.NΔ Y → (letE i : LetA O n) • y = y → W.map π (W.π₀ ^ k • y) = 0 → ∃ m, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i m ∧ W.map ι m = y`. Introduce `k y i hy hyi h0`. Rewrite `h0` using `[Relay2.mapA_smul]`. Take `⟨m, hm⟩` from `hmid y (cancel_unit_mul_uniformizer_pow W hu W.one k h0)`. Establish `hmN : m ∈ W.N T₂` using `h6d m (by rw [hm]; exact hy.1)`.

Use `⟨m, Relay2.InNΔi_of W T₂ i ⟨hmN, fun δ hδ => inj _ _ ?_⟩ (inj _ _ ?_), hm⟩` and prove the remaining obligations. Rewrite using `[W.map_γ, hm, hy.2 δ hδ]`. Rewrite using `[Relay2.mapA_smul, hm, hyi]`. Establish `hSP` using `SatPW.satPCore_of W hinj h9`. Establish `hpull : ∀ c ∈ A.cuts, ∀ (e' : ℕ) (z : W.DD T₂), W.map ι z ∈ Pp W Y c e' → z ∈ Pp W T₂ c e'`.

Introduce `c hc e' z hz`. Establish `hy0N : (letE c : LetA O n) • e ∈ W.Nl W.one c` using `⟨e, heN, rfl⟩`. Establish `hy0Δ : ∀ g, W.γD W.one g ((letE c : LetA O n) • e) = (letE c : LetA O n) • e` using `fun g => by`. Rewrite using `[γD_letE, heγ]`. Take `⟨z₁, hz₁N, hz₁π⟩` from `hK c hc _ hy0N (fun δ _ => hy0Δ δ)`.

Rewrite `hz₁π` using `[LinearMap.restrictScalars_apply]`. Take `⟨y₁, hy₁, hy₁π⟩` from `lift_avg W (hΔu hCA) π c hz₁N hz₁π (fun δ _ => by`. Rewrite using `[γD_smulA, hy0Δ]`. Simplify using `[Formalism.MainNotions.LiftingTheory.lp])`. Establish `h1` using `pp_pull W hinj hone.1 hY hmid hinjι hπι h6d heSpan heφ heγ c (W.AΔ.pow_mem (Relay2.lA_mem W) rr) hy₁ hy₁π e' z hz`.

Rewrite `h1` using `[Split.φA_pow_lA]`. Establish `hJY : Formalism.MainNotions.LiftingTheory.JumpsLet W Y (fun i => PhiPowers.Mw A.G₀ A.S A.η (A.ty i)) (fun i => PhiPowers.Hw A.G₀ A.S A.η (A.ty i))` using `fun i τ hτ a ha => PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hWY.2 i τ hτ a ha)`. Take `⟨z₂, hz₂N, hz₂π⟩` from `hWX Y W.one π _ _ ⟨hY, hone.1, hses.2.2.1⟩ hJY c _ hy0N`. Rewrite `hz₂π` using `[LinearMap.restrictScalars_apply]`. Use `set H := Formalism.MainNotions.LiftingTheory.Hmax n (fun i => PhiPowers.Mw A.G₀ A.S A.η (A.ty i)) (fun i => PhiPowers.Hw A.G₀ A.S A.η (A.ty i)) with hHdef`.

Establish `hX : W.X = letπ` using `by simp [LocWach.X, hCA.2.1]`. Take `⟨wu, hwu⟩` from `hR9Y.1.2.2.1`. Establish `hHle : H ≤ (PD.p - 1) * H` using `Nat.le_mul_of_pos_left H (by omega)`. Establish `hπ₀H : W.π₀ ^ H = ((wu : LetA O n) ^ H * letπ ^ ((PD.p - 1) * H - H)) * W.X ^ H`. Rewrite using `[hX, hwu, mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hHle]`.

Establish `hz₂' : W.map π (((wu : LetA O n) ^ H * letπ ^ ((PD.p - 1) * H - H)) • z₂) = W.π₀ ^ H • ((letE c : LetA O n) • e)`. Rewrite using `[Relay2.mapA_smul, hz₂π, smul_smul, ← hπ₀H]`. Take `⟨y₂, hy₂, hy₂π⟩` from `lift_avg W (hΔu hCA) π c ((W.Nl Y c).smul_mem _ hz₂N) hz₂' (fun δ hδ => by rw [γD_smulA, hy0Δ, (W.AΔ.pow_mem hπ H) δ hδ])`. Establish `h2` using `pp_pull W hinj hone.1 hY hmid hinjι hπι h6d heSpan heφ heγ c (W.AΔ.pow_mem hπ H) hy₂ hy₂π e' z hz`. Take `⟨u, -, u', hu'Δ, huu', hTr2⟩` from `(hTr hCA).2.1 e' H`.

Establish `hf' : W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H) ∈ PiPs W`. Use `Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert _ _)) _) (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ ?_ _)` and prove the remaining obligations. Conclude with `Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨k, rfl⟩)`. Establish `hfx : InFP W T₂ c e' 1 ((W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H)) • z)`. Use `⟨_, ?_, (one_smul _ _).symm⟩` and prove the remaining obligations.

Establish `e1 : u' • ((W.φA ^ e') (W.π₀ ^ H) • z) = (W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H)) • z`. Rewrite using `[map_pow, hTr2, smul_smul]`. Use `congr 1`. Take the linear combination `(W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H)) * huu'`. Rewrite using `[← e1]`.

Conclude with `Relay2.Pp_smul W T₂ c e' hu'Δ _ h2`. Take `⟨y, hy, hyz⟩` from `hSP hCA T₂ c e' 1 _ hT₂c (Submonoid.one_mem _) hf' z hfx ⟨rr, lA W ^ rr • z, h1, (one_smul _ _).symm⟩`. Rewrite using `[hyz, one_smul]`. Conclude with `hy`. Establish `hloc : ∀ c : ZMod n, ∃ (x : W.DD Y) (u' τ m : W.DD T₂), c ∈ A.cuts → (Formalism.MainNotions.LiftingTheory.InNΔi W Y c x ∧ W.map π x = (b * ((PD.p : ℕ) : O) ^ rr) • ((letE c : LetA O n) • e)) ∧ Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c u' ∧ W.map ι (W.π₀ • u') = W.γ Y x - x …`.

Introduce `c`. Distinguish the cases in `hc : c ∈ A.cuts`. Use `swap`. Conclude with `⟨0, 0, 0, 0, fun h => absurd h hc⟩`. Establish `hy0N : (letE c : LetA O n) • e ∈ W.Nl W.one c` using `⟨e, heN, rfl⟩`.

Establish `hy0Δ : ∀ g, W.γD W.one g ((letE c : LetA O n) • e) = (letE c : LetA O n) • e` using `fun g => by`. Rewrite using `[γD_letE, heγ]`. Take `⟨x', hx'N, hx'π⟩` from `hK c hc _ hy0N (fun δ _ => hy0Δ δ)`. Rewrite `hx'π` using `[LinearMap.restrictScalars_apply]`. Use `set s : W.DD Y := ∑ g ∈ W.DelF, W.γD Y g x' with hs`.

Use `set r : O := b * (((hΔu hCA).unit⁻¹ : Oˣ) : O) with hr`. Use `set x : W.DD Y := r • s with hxdef`. Establish `hsNl : s ∈ W.Nl Y c` using `Submodule.sum_mem _ fun g _ => γD_Nl W g hx'N`. Establish `hxNl : x ∈ W.Nl Y c` using `(W.Nl Y c).smul_of_tower_mem r hsNl`. Establish `hxΔ : ∀ δ ∈ W.DelF, W.γD Y δ x = x` using `fun δ hδ => by`.

Rewrite using `[hxdef, map_smul, sumΔ_inv W Y x' δ hδ]`. Establish `hxNΔ : x ∈ W.NΔ Y` using `⟨N_of_Nl W hxNl, hxΔ⟩`. Establish `hxi : Formalism.MainNotions.LiftingTheory.InNΔi W Y c x` using `⟨hxNΔ, hxNl⟩`. Establish `hxc : (letE c : LetA O n) • x = x` using `letE_of_Nl W hxNl`. Establish `hxπ : W.map π x = (b * ((PD.p : ℕ) : O) ^ rr) • ((letE c : LetA O n) • e)`.

Establish `h1 : ∀ g ∈ W.DelF, W.map π (W.γD Y g x') = Formalism.MainNotions.LiftingTheory.lp W rr • ((letE c : LetA O n) • e)` using `fun g _ => by`. Rewrite using `[W.map_γ, hx'π, γD_smulA, hy0Δ]`. Simplify using `[Formalism.MainNotions.LiftingTheory.lp]`. Rewrite using `[hxdef, LinearMap.map_smul_of_tower, hs, map_sum, Finset.sum_congr rfl h1, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, smul_smul, show Formalism.MainNotions.LiftingTheory.lp W rr = lA W ^ rr from rfl, Split.lA_pow_smul, smul_smul]`. Use `congr 1`.

Establish `hcu : (((hΔu hCA).unit⁻¹ : Oˣ) : O) * ((W.DelF.card : ℕ) : O) = 1` using `(hΔu hCA).val_inv_mul`. Take the linear combination `(b * ((PD.p : ℕ) : O) ^ rr) * hcu`. Take `⟨x'', hx''N, hx''⟩` from `hR9Y.2.2 x hxNΔ`. Establish `hx''c : (letE c : LetA O n) • x'' = x''`. Establish `h0 : W.π₀ ^ 1 • ((letE c : LetA O n) • x'' - x'') = 0`.

Rewrite using `[pow_one, smul_sub, smul_comm, ← hx'', smul_sub, ← γ_letE, hxc, sub_self]`. Conclude with `sub_eq_zero.1 (cancel_unit_mul_uniformizer_pow W hu Y 1 h0)`. Establish `hπx : W.γ W.one (W.map π x) = W.map π x`. Rewrite using `[hxπ, map_smul, γ_letE]`. Use `congr 1`.

Use `show (letE c : LetA O n) • W.γD W.one W.gam e = _`. Rewrite using `[heγ]`. Take `⟨u', hu'i, hu'⟩` from `pull 1 x'' c hx''N hx''c (by`. Rewrite using `[pow_one, ← hx'', map_sub, hγπ, hπx, sub_self])`. Establish `hu'x : W.map ι (W.π₀ • u') = W.γ Y x - x`.

Rewrite using `[Relay2.mapA_smul, hu', hx'']`. Take `⟨d, bb, cf, hbb, hsol, hc0, hbd⟩` from `Relay2.solData W T₂ c hR9.2 (hH hCA T₂ hT₂c c).2.2.1 (W.π₀ • u') ⟨u', hu'i, rfl⟩`. Take `⟨τ, hτ, hG⟩` from `Relay2.tauZ_exists W T₂ hC hR9.1 hCA.2.2 A hA.2.1 c (W.π₀ • u') bb cf hbb hsol hc0 hbd (hH hCA T₂ hT₂c c).2.2.2.1`. Establish `hGY : Relay2.Good W Y c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) x (W.map ι τ)`. Use `Relay2.goodZ_map W ι hT₂c hY c A.j _ _ _ hG` as an intermediate fact.

Rewrite `this` using `[hu'x]`. Conclude with `this`. Establish `hτY : InFP W Y c A.j W.π₀ (W.map ι τ)` using `Relay2.inMultiple_map W ι hT₂c hY c A.j _ hτ`. Establish `hx''i : Formalism.MainNotions.LiftingTheory.InNΔi W Y c x''` using `Relay2.InNΔi_of W Y c hx''N hx''c`. Establish `hTrY` using `Relay2.mkTr W hinj hO2 h9 hH hTr hCA Y hY A hM c ⟨x'', hx''i, hx''⟩ hτY hGY`.

Establish `hIx : InI W Y c x` using `⟨hxc, hxΔ, ⟨x'', hx''N, hx''c, hx''⟩⟩`. Establish `hcl` using `(((hRel hCA h5 A hA c hc).1 Y hWY).2.1 x hIx).2.2.1 (W.map ι τ) hTrY`. Take `⟨y', hy'N, hy'c, hy'⟩` from `hcl`. Establish `hfix : W.γ W.one (W.map π (lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) x - W.map ι τ)) = W.map π (lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) x - W.map ι τ)`. Rewrite using `[map_sub, hπι, sub_zero, Relay2.mapA_smul, Relay2.map_φpow, Relay2.γ_lsmul, Split.γ_φpow, hπx]`.

Take `⟨m, hmi, hm⟩` from `pull (A.M PD.p) y' (c + (A.j : ZMod n)) hy'N hy'c (by`. Rewrite using `[← hy', map_sub, hγπ, hfix, sub_self])`. Conclude with `⟨x, u', τ, m, fun _ => ⟨⟨hxi, hxπ⟩, hu'i, hu'x, hτ, hG, hmi, by`. Rewrite using `[hy', ← hm, Relay2.mapA_smul]⟩⟩`. Use `choose x u' τ m hL using hloc`.

Establish `hXP : ∀ c ∈ A.cuts, Split.xsh W A ι x τ c ∈ Pp W Y c A.j` using `fun c hc => (Pp W Y c A.j).sub_mem (Relay2.Pp_smul W Y c A.j (W.AΔ.pow_mem (Relay2.lA_mem W) _) _ (Relay2.Pp_phi W Y c A.j (hL c hc).1.1)) (Relay2.Pp_map W ι hT₂c hY c A.j _ (Relay2.mem_Pp_of_inMultiple W T₂ c A.j hπ (hL c hc).2.2.2.1))`. Use `⟨x, τ, m, fun c hc => ?_⟩` and prove the remaining obligations. Take `⟨⟨hxi, hxπ⟩, hu'i, hu'x, hτ, hG, hmi, hγX⟩` from `hL c hc`. Use `⟨hxi.2, hxπ, hXP c hc, Relay2.Pp_Δ W Y c A.j _ (hXP c hc), hmi.1, hγX, fun w hw => ?_⟩` and prove the remaining obligations. Use `set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'def`.

Establish `hc' : c' ∈ A.cuts` using `(hA.2.2.1 c hc).2.2.1`. Establish `hjl : A.j ≤ A.len c` using `hA.2.2.2.1 c hc`. Take `⟨-, -, -, -, -, hmi', hγX'⟩` from `hL c' hc'`. Establish `hX'` using `hXP c' hc'`. Establish `hidx : c' + (A.j : ZMod n) + ((A.len c - A.j : ℕ) : ZMod n) = c`.

Rewrite using `[hc'def, Nat.cast_sub hjl]`. Expand and normalize the polynomial expressions, which then agree. Establish `hXl` using `Relay2.Pp_letter W Y c' A.j _ hX'`. Establish `hφXl : (letE c : LetA O n) • ((W.φD Y) ^ (A.len c - A.j)) (Split.xsh W A ι x τ c') = ((W.φD Y) ^ (A.len c - A.j)) (Split.xsh W A ι x τ c')`. Use `PhiPowers.φD_pow_letter W Y (c' + (A.j : ZMod n)) _ hXl (A.len c - A.j)` as an intermediate fact.

Rewrite `this` using `[hidx]`. Then use the resulting hypothesis. Establish `hxc : (letE c : LetA O n) • x c = x c` using `Relay2.InNΔi_letter W Y c hxi`. Establish `hwc : (letE c : LetA O n) • w = w` using `inj _ _ (by`. Rewrite using `[Relay2.mapA_smul, hw, smul_sub, hφXl, smul_comm (letE c : LetA O n) (lA W ^ A.σ PD.p), hxc])`. Establish `hXΔ'` using `Relay2.Pp_Δ W Y c' A.j _ hX'`.

Establish `hwΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ w = w` using `fun δ hδ => inj _ _ (by`. Rewrite using `[W.map_γ, hw, map_sub, PhiPowers.φD_pow_Δ W Y hXΔ' (A.len c - A.j) δ hδ, γD_lA, hxi.1.2 δ hδ])`. Establish `e1 : W.map ι (W.γ T₂ w - w) = W.γ Y (W.map ι w) - W.map ι w` using `by rw [map_sub, hγι]`. Establish `e2 : W.map ι (((W.φD T₂) ^ (A.len c - A.j)) (W.π₀ ^ A.M PD.p • m c') - lA W ^ A.σ PD.p • (W.π₀ • u' c)) = ((W.φD Y) ^ (A.len c - A.j)) (W.γ Y (Split.xsh W A ι x τ c') - Split.xsh W A ι x τ c') - lA W ^ A.σ PD.p • (W.γ Y (x c) - x c)`. Rewrite using `[map_sub, Relay2.map_φpow, Relay2.mapA_smul W ι (lA W ^ A.σ PD.p), hu'x]`.

Use `congr 2`. Conclude with `hγX'.symm`. Establish `e3 : W.γ Y (W.map ι w) - W.map ι w = ((W.φD Y) ^ (A.len c - A.j)) (W.γ Y (Split.xsh W A ι x τ c') - Split.xsh W A ι x τ c') - lA W ^ A.σ PD.p • (W.γ Y (x c) - x c)`. Rewrite using `[hw, map_sub (W.γ Y), Split.γ_φpow, Relay2.γ_lsmul, map_sub ((W.φD Y) ^ (A.len c - A.j)), smul_sub]`. Normalize the expressions using the abelian group laws.

Establish `hγw : W.γ T₂ w - w = ((W.φD T₂) ^ (A.len c - A.j)) (W.π₀ ^ A.M PD.p • m c') - lA W ^ A.σ PD.p • (W.π₀ • u' c)` using `inj _ _ (e1.trans (e3.trans e2.symm))`. Take `⟨y'', hy''N, hy''⟩` from `Split.InFN_φpow W T₂ (A.M PD.p) hq hF1a hmi'.1 (A.len c - A.j)`. Establish `hml : (letE (c' + (A.j : ZMod n)) : LetA O n) • (W.π₀ ^ A.M PD.p • m c') = W.π₀ ^ A.M PD.p • m c'`. Rewrite using `[smul_comm, Relay2.InNΔi_letter W T₂ _ hmi']`. Establish `hφml` using `PhiPowers.φD_pow_letter W T₂ _ _ hml (A.len c - A.j)`.

Rewrite `hφml` using `[hidx, hy'']`. Establish `hy''c : (letE c : LetA O n) • y'' = y''`. Establish `h0 : W.π₀ ^ A.M PD.p • ((letE c : LetA O n) • y'' - y'') = 0`. Rewrite using `[smul_sub, smul_comm, hφml, sub_self]`. Conclude with `sub_eq_zero.1 (cancel_unit_mul_uniformizer_pow W hu T₂ _ h0)`.

Establish `hy''i : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c y''` using `Relay2.InNΔi_of W T₂ c hy''N hy''c`. Take `⟨M', hM'⟩ : ∃ M', A.M PD.p = M' + 1` from `⟨A.M PD.p - 1, by have := Relay2.M_pos A PD.p; omega⟩`. Use `set z₀ : W.DD T₂ := W.π₀ ^ M' • y'' - lA W ^ A.σ PD.p • u' c with hz₀`. Establish `hz₀i : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c z₀` using `Relay2.InNΔi_sub W T₂ c (Relay2.InNΔi_smul W T₂ c (W.AΔ.pow_mem hπ _) hy''i) (Relay2.InNΔi_lsmul W T₂ c _ hu'i)`. Establish `hγw' : W.γ T₂ w - w = W.π₀ • z₀`.

Rewrite using `[hγw, hy'', hM', hz₀]`. Conclude with `lin3 _ _ _ _ _ _`. Establish `hIw : InI W T₂ c w` using `⟨hwc, hwΔ, ⟨z₀, hz₀i.1, Relay2.InNΔi_letter W T₂ c hz₀i, hγw'⟩⟩`. Establish `hΛ : abelian₂ W A c (A.len c) ∈ W.AΔ` using `W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (PhiPowers.ps_mem_AΔ W hπ s) _`. Establish `hAr` using `hArc hCA h5 A hA c hc (A.len c) hjl le_rfl`.

Simplify using `only at hAr`. Establish `hca : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c` using `sub_add_cancel _ _`. Rewrite `hAr` using `[hca]`. Establish `hΛx : abelian₂ W A c (A.len c) • x c ∈ Pp W Y c' (A.len c)`. Take `⟨y, hy, hyeq⟩` from `(hAr.2 Y hWY).2.1 (x c) ⟨x c, hxi.1, hxc, (one_smul _ _).symm⟩`.

Rewrite using `[hyeq, one_smul]`. Conclude with `hy`. Establish `hφX : ((W.φD Y) ^ (A.len c - A.j)) (Split.xsh W A ι x τ c') ∈ Pp W Y c' (A.len c)`. Use `Split.Pp_φpow W Y c' A.j (A.len c - A.j) hX'` as an intermediate fact. Rewrite `this` using `[Nat.add_sub_cancel' hjl]`. Then use the resulting hypothesis.

Establish `hιΛw : W.map ι (abelian₂ W A c (A.len c) • w) ∈ Pp W Y c' (A.len c)`. Rewrite using `[Relay2.mapA_smul, hw, smul_sub, smul_comm (abelian₂ W A c (A.len c)) (lA W ^ A.σ PD.p)]`. Conclude with `(Pp W Y c' (A.len c)).sub_mem (Relay2.Pp_smul W Y c' _ hΛ _ hφX) (Relay2.Pp_smul W Y c' _ (W.AΔ.pow_mem (Relay2.lA_mem W) _) _ hΛx)`. Establish `hPw : InFP W T₂ c' (A.len c) 1 (abelian₂ W A c (A.len c) • w)` using `⟨_, hpull c' hc' (A.len c) _ hιΛw, (one_smul _ _).symm⟩`. Establish `hGw : Relay2.Good W T₂ c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) w (-(lA W ^ A.σ PD.p • τ c))` using `(Relay2.good_iff W T₂ c _ _ _ _ w _).2 (Relay2.goodZ_comb W T₂ c A.j _ _ _ hG hy''i (by rw [hγw, hy'']))`.

Establish `hτw : InFP W T₂ c A.j W.π₀ (-(lA W ^ A.σ PD.p • τ c))` using `Relay2.inMultiple_neg W T₂ c A.j _ (Relay2.inMultiple_lA_pow_smul W T₂ c A.j _ _ hτ)`. Conclude with `⟨hIw, hPw, Relay2.mkTr W hinj hO2 h9 hH hTr hCA T₂ hT₂c A hM c ⟨z₀, hz₀i, hγw'⟩ hτw hGw⟩`.
-/
theorem cutData_of [NeZero n] [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hone : IsCrys PD W.one.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD W.one.ρ τ a → a = 0)
    (hΔu : Formalism.MainNotions.LiftingTheory.CaseA W → IsUnit ((W.DelF.card : ℕ) : O))
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W) (hH : Formalism.MainNotions.LiftingTheory.coreH W)
    (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hJ : Formalism.MainNotions.LiftingTheory.coreJumps PD LL O) (hF1 : FirstWachFiltration W)
    (hRel : RelayCore W) (hArc : ArcCore W) (hEx : Split.DDExact W) (hWX : Formalism.MainNotions.LiftingTheory.coreWX W) :
    Split.CutData W := by
  intro hCA h5 A hA T₂ Y ι π hT₂ hY hses rr hK e heN heSpan heφ heγ b
  have hT₂c : IsCrys PD T₂.ρ := hT₂.1
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨hπι, hinjι, hmid⟩ := hEx T₂ Y ι π hT₂c hY hses
  have inj : ∀ x x' : W.DD T₂, W.map ι x = W.map ι x' → x = x' := fun x x' h =>
    sub_eq_zero.1 (hinjι _ (by rw [map_sub, h, sub_self]))
  have h6d : ∀ x : W.DD T₂, W.map ι x ∈ W.N Y → x ∈ W.N T₂ :=
    (h6.2.2 T₂ Y W.one ι π hT₂c hY hone.1 hses).2.2.2.1
  have hR9Y := Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA Y hY
  have hR9 := Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hCA T₂ hT₂c
  have hu := uniformizer_isUnit_etale W hR9Y.1.2.2.1
  have hπ : W.π₀ ∈ W.AΔ := hR9Y.1.1
  have hWY : Win W A Y := win_ext W A hJ hone hT₂ hY hses
  have hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p := Relay2.arith_M PD.p A.G₀ A.h hl hA.2.2.2.2.2.1
  have hlt : A.h < (PD.p - 1) * A.M PD.p := Split.arith_h PD.p A.h hl
  have hJ2 := Split.jumpsLe_of_win W A hA T₂ hT₂
  have hF1a := ((hF1 hCA A.h (A.M PD.p) hlt).1 T₂ hT₂c hJ2).1
  have hq : qA W ∈ W.AΔ := W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
  have hγι : ∀ z : W.DD T₂, W.map ι (W.γ T₂ z) = W.γ Y (W.map ι z) := fun z => W.map_γ ι W.gam z
  have hγπ : ∀ z : W.DD Y, W.map π (W.γ Y z) = W.γ W.one (W.map π z) := fun z => W.map_γ π W.gam z
  have hCY := Relay2.ctx_of W hinj hO2 h9 hH hTr hCA Y hY
  have hC := Relay2.ctx_of W hinj hO2 h9 hH hTr hCA T₂ hT₂c

  have pull : ∀ (k : ℕ) (y : W.DD Y) (i : ZMod n), y ∈ W.NΔ Y → (letE i : LetA O n) • y = y →
      W.map π (W.π₀ ^ k • y) = 0 → ∃ m, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ i m ∧ W.map ι m = y := by
    intro k y i hy hyi h0
    rw [Relay2.mapA_smul] at h0
    obtain ⟨m, hm⟩ := hmid y (cancel_unit_mul_uniformizer_pow W hu W.one k h0)
    have hmN : m ∈ W.N T₂ := h6d m (by rw [hm]; exact hy.1)
    refine ⟨m, Relay2.InNΔi_of W T₂ i ⟨hmN, fun δ hδ => inj _ _ ?_⟩ (inj _ _ ?_), hm⟩
    · rw [W.map_γ, hm, hy.2 δ hδ]
    · rw [Relay2.mapA_smul, hm, hyi]

  have hSP := SatPW.satPCore_of W hinj h9
  have hpull : ∀ c ∈ A.cuts, ∀ (e' : ℕ) (z : W.DD T₂), W.map ι z ∈ Pp W Y c e' → z ∈ Pp W T₂ c e' := by
    intro c hc e' z hz
    have hy0N : (letE c : LetA O n) • e ∈ W.Nl W.one c := ⟨e, heN, rfl⟩
    have hy0Δ : ∀ g, W.γD W.one g ((letE c : LetA O n) • e) = (letE c : LetA O n) • e := fun g => by
      rw [γD_letE, heγ]

    obtain ⟨z₁, hz₁N, hz₁π⟩ := hK c hc _ hy0N (fun δ _ => hy0Δ δ)
    rw [LinearMap.restrictScalars_apply] at hz₁π
    obtain ⟨y₁, hy₁, hy₁π⟩ := lift_avg W (hΔu hCA) π c hz₁N hz₁π (fun δ _ => by
      rw [γD_smulA, hy0Δ]; simp [Formalism.MainNotions.LiftingTheory.lp])
    have h1 := pp_pull W hinj hone.1 hY hmid hinjι hπι h6d heSpan heφ heγ c
      (W.AΔ.pow_mem (Relay2.lA_mem W) rr) hy₁ hy₁π e' z hz
    rw [Split.φA_pow_lA] at h1

    have hJY : Formalism.MainNotions.LiftingTheory.JumpsLet W Y (fun i => PhiPowers.Mw A.G₀ A.S A.η (A.ty i))
        (fun i => PhiPowers.Hw A.G₀ A.S A.η (A.ty i)) := fun i τ hτ a ha =>
      PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hWY.2 i τ hτ a ha)
    obtain ⟨z₂, hz₂N, hz₂π⟩ := hWX Y W.one π _ _ ⟨hY, hone.1, hses.2.2.1⟩ hJY c _ hy0N
    rw [LinearMap.restrictScalars_apply] at hz₂π
    set H := Formalism.MainNotions.LiftingTheory.Hmax n (fun i => PhiPowers.Mw A.G₀ A.S A.η (A.ty i))
      (fun i => PhiPowers.Hw A.G₀ A.S A.η (A.ty i)) with hHdef
    have hX : W.X = letπ := by simp [LocWach.X, hCA.2.1]
    obtain ⟨wu, hwu⟩ := hR9Y.1.2.2.1
    have hHle : H ≤ (PD.p - 1) * H := Nat.le_mul_of_pos_left H (by omega)
    have hπ₀H : W.π₀ ^ H = ((wu : LetA O n) ^ H * letπ ^ ((PD.p - 1) * H - H)) * W.X ^ H := by
      rw [hX, hwu, mul_pow, ← pow_mul, mul_assoc, ← pow_add, Nat.sub_add_cancel hHle]
    have hz₂' : W.map π (((wu : LetA O n) ^ H * letπ ^ ((PD.p - 1) * H - H)) • z₂) =
        W.π₀ ^ H • ((letE c : LetA O n) • e) := by
      rw [Relay2.mapA_smul, hz₂π, smul_smul, ← hπ₀H]
    obtain ⟨y₂, hy₂, hy₂π⟩ := lift_avg W (hΔu hCA) π c ((W.Nl Y c).smul_mem _ hz₂N) hz₂'
      (fun δ hδ => by rw [γD_smulA, hy0Δ, (W.AΔ.pow_mem hπ H) δ hδ])
    have h2 := pp_pull W hinj hone.1 hY hmid hinjι hπι h6d heSpan heφ heγ c
      (W.AΔ.pow_mem hπ H) hy₂ hy₂π e' z hz

    obtain ⟨u, -, u', hu'Δ, huu', hTr2⟩ := (hTr hCA).2.1 e' H
    have hf' : W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H) ∈ PiPs W := by
      refine Submonoid.mul_mem _ (Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert _ _)) _)
        (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ ?_ _)
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨k, rfl⟩)
    have hfx : InFP W T₂ c e' 1
        ((W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H)) • z) := by
      refine ⟨_, ?_, (one_smul _ _).symm⟩
      have e1 : u' • ((W.φA ^ e') (W.π₀ ^ H) • z) =
          (W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H)) • z := by
        rw [map_pow, hTr2, smul_smul]
        congr 1
        linear_combination (W.π₀ ^ H * ∏ k ∈ Finset.range e', Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * H)) * huu'
      rw [← e1]
      exact Relay2.Pp_smul W T₂ c e' hu'Δ _ h2
    obtain ⟨y, hy, hyz⟩ := hSP hCA T₂ c e' 1 _ hT₂c (Submonoid.one_mem _) hf' z hfx
      ⟨rr, lA W ^ rr • z, h1, (one_smul _ _).symm⟩
    rw [hyz, one_smul]
    exact hy

  have hloc : ∀ c : ZMod n, ∃ (x : W.DD Y) (u' τ m : W.DD T₂), c ∈ A.cuts →
      (Formalism.MainNotions.LiftingTheory.InNΔi W Y c x ∧
        W.map π x = (b * ((PD.p : ℕ) : O) ^ rr) • ((letE c : LetA O n) • e)) ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c u' ∧ W.map ι (W.π₀ • u') = W.γ Y x - x ∧
      InFP W T₂ c A.j W.π₀ τ ∧
      Relay2.GoodZ W T₂ c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) (W.π₀ • u') τ ∧
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c + (A.j : ZMod n)) m ∧
      W.γ Y (lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) x - W.map ι τ) -
          (lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) x - W.map ι τ) = W.map ι (W.π₀ ^ A.M PD.p • m) := by
    intro c
    by_cases hc : c ∈ A.cuts
    swap
    · exact ⟨0, 0, 0, 0, fun h => absurd h hc⟩

    have hy0N : (letE c : LetA O n) • e ∈ W.Nl W.one c := ⟨e, heN, rfl⟩
    have hy0Δ : ∀ g, W.γD W.one g ((letE c : LetA O n) • e) = (letE c : LetA O n) • e := fun g => by
      rw [γD_letE, heγ]
    obtain ⟨x', hx'N, hx'π⟩ := hK c hc _ hy0N (fun δ _ => hy0Δ δ)
    rw [LinearMap.restrictScalars_apply] at hx'π
    set s : W.DD Y := ∑ g ∈ W.DelF, W.γD Y g x' with hs
    set r : O := b * (((hΔu hCA).unit⁻¹ : Oˣ) : O) with hr
    set x : W.DD Y := r • s with hxdef
    have hsNl : s ∈ W.Nl Y c := Submodule.sum_mem _ fun g _ => γD_Nl W g hx'N
    have hxNl : x ∈ W.Nl Y c := (W.Nl Y c).smul_of_tower_mem r hsNl
    have hxΔ : ∀ δ ∈ W.DelF, W.γD Y δ x = x := fun δ hδ => by
      rw [hxdef, map_smul, sumΔ_inv W Y x' δ hδ]
    have hxNΔ : x ∈ W.NΔ Y := ⟨N_of_Nl W hxNl, hxΔ⟩
    have hxi : Formalism.MainNotions.LiftingTheory.InNΔi W Y c x := ⟨hxNΔ, hxNl⟩
    have hxc : (letE c : LetA O n) • x = x := letE_of_Nl W hxNl
    have hxπ : W.map π x = (b * ((PD.p : ℕ) : O) ^ rr) • ((letE c : LetA O n) • e) := by
      have h1 : ∀ g ∈ W.DelF, W.map π (W.γD Y g x') =
          Formalism.MainNotions.LiftingTheory.lp W rr • ((letE c : LetA O n) • e) := fun g _ => by
        rw [W.map_γ, hx'π, γD_smulA, hy0Δ]
        simp [Formalism.MainNotions.LiftingTheory.lp]
      rw [hxdef, LinearMap.map_smul_of_tower, hs, map_sum, Finset.sum_congr rfl h1, Finset.sum_const,
        ← Nat.cast_smul_eq_nsmul O, smul_smul, show Formalism.MainNotions.LiftingTheory.lp W rr = lA W ^ rr from rfl,
        Split.lA_pow_smul, smul_smul]
      congr 1
      have hcu : (((hΔu hCA).unit⁻¹ : Oˣ) : O) * ((W.DelF.card : ℕ) : O) = 1 :=
        (hΔu hCA).val_inv_mul
      linear_combination (b * ((PD.p : ℕ) : O) ^ rr) * hcu

    obtain ⟨x'', hx''N, hx''⟩ := hR9Y.2.2 x hxNΔ
    have hx''c : (letE c : LetA O n) • x'' = x'' := by
      have h0 : W.π₀ ^ 1 • ((letE c : LetA O n) • x'' - x'') = 0 := by
        rw [pow_one, smul_sub, smul_comm, ← hx'', smul_sub, ← γ_letE, hxc, sub_self]
      exact sub_eq_zero.1 (cancel_unit_mul_uniformizer_pow W hu Y 1 h0)
    have hπx : W.γ W.one (W.map π x) = W.map π x := by
      rw [hxπ, map_smul, γ_letE]
      congr 1
      show (letE c : LetA O n) • W.γD W.one W.gam e = _
      rw [heγ]
    obtain ⟨u', hu'i, hu'⟩ := pull 1 x'' c hx''N hx''c (by
      rw [pow_one, ← hx'', map_sub, hγπ, hπx, sub_self])
    have hu'x : W.map ι (W.π₀ • u') = W.γ Y x - x := by
      rw [Relay2.mapA_smul, hu', hx'']

    obtain ⟨d, bb, cf, hbb, hsol, hc0, hbd⟩ := Relay2.solData W T₂ c hR9.2 (hH hCA T₂ hT₂c c).2.2.1
      (W.π₀ • u') ⟨u', hu'i, rfl⟩
    obtain ⟨τ, hτ, hG⟩ := Relay2.tauZ_exists W T₂ hC hR9.1 hCA.2.2 A hA.2.1 c (W.π₀ • u') bb cf hbb
      hsol hc0 hbd (hH hCA T₂ hT₂c c).2.2.2.1

    have hGY : Relay2.Good W Y c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) x (W.map ι τ) := by
      have := Relay2.goodZ_map W ι hT₂c hY c A.j _ _ _ hG
      rw [hu'x] at this
      exact this
    have hτY : InFP W Y c A.j W.π₀ (W.map ι τ) := Relay2.inMultiple_map W ι hT₂c hY c A.j _ hτ
    have hx''i : Formalism.MainNotions.LiftingTheory.InNΔi W Y c x'' := Relay2.InNΔi_of W Y c hx''N hx''c
    have hTrY := Relay2.mkTr W hinj hO2 h9 hH hTr hCA Y hY A hM c ⟨x'', hx''i, hx''⟩ hτY hGY
    have hIx : InI W Y c x := ⟨hxc, hxΔ, ⟨x'', hx''N, hx''c, hx''⟩⟩
    have hcl := (((hRel hCA h5 A hA c hc).1 Y hWY).2.1 x hIx).2.2.1 (W.map ι τ) hTrY
    obtain ⟨y', hy'N, hy'c, hy'⟩ := hcl

    have hfix : W.γ W.one (W.map π (lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) x - W.map ι τ)) =
        W.map π (lA W ^ A.σ PD.p • ((W.φD Y) ^ A.j) x - W.map ι τ) := by
      rw [map_sub, hπι, sub_zero, Relay2.mapA_smul, Relay2.map_φpow, Relay2.γ_lsmul, Split.γ_φpow,
        hπx]
    obtain ⟨m, hmi, hm⟩ := pull (A.M PD.p) y' (c + (A.j : ZMod n)) hy'N hy'c (by
      rw [← hy', map_sub, hγπ, hfix, sub_self])
    exact ⟨x, u', τ, m, fun _ => ⟨⟨hxi, hxπ⟩, hu'i, hu'x, hτ, hG, hmi, by
      rw [hy', ← hm, Relay2.mapA_smul]⟩⟩
  choose x u' τ m hL using hloc
  have hXP : ∀ c ∈ A.cuts, Split.xsh W A ι x τ c ∈ Pp W Y c A.j := fun c hc =>
    (Pp W Y c A.j).sub_mem (Relay2.Pp_smul W Y c A.j (W.AΔ.pow_mem (Relay2.lA_mem W) _) _
      (Relay2.Pp_phi W Y c A.j (hL c hc).1.1))
      (Relay2.Pp_map W ι hT₂c hY c A.j _ (Relay2.mem_Pp_of_inMultiple W T₂ c A.j hπ (hL c hc).2.2.2.1))
  refine ⟨x, τ, m, fun c hc => ?_⟩
  obtain ⟨⟨hxi, hxπ⟩, hu'i, hu'x, hτ, hG, hmi, hγX⟩ := hL c hc
  refine ⟨hxi.2, hxπ, hXP c hc, Relay2.Pp_Δ W Y c A.j _ (hXP c hc), hmi.1, hγX, fun w hw => ?_⟩
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'def
  have hc' : c' ∈ A.cuts := (hA.2.2.1 c hc).2.2.1
  have hjl : A.j ≤ A.len c := hA.2.2.2.1 c hc
  obtain ⟨-, -, -, -, -, hmi', hγX'⟩ := hL c' hc'
  have hX' := hXP c' hc'
  have hidx : c' + (A.j : ZMod n) + ((A.len c - A.j : ℕ) : ZMod n) = c := by
    rw [hc'def, Nat.cast_sub hjl]; ring
  have hXl := Relay2.Pp_letter W Y c' A.j _ hX'
  have hφXl : (letE c : LetA O n) • ((W.φD Y) ^ (A.len c - A.j)) (Split.xsh W A ι x τ c') =
      ((W.φD Y) ^ (A.len c - A.j)) (Split.xsh W A ι x τ c') := by
    have := PhiPowers.φD_pow_letter W Y (c' + (A.j : ZMod n)) _ hXl (A.len c - A.j)
    rwa [hidx] at this
  have hxc : (letE c : LetA O n) • x c = x c := Relay2.InNΔi_letter W Y c hxi

  have hwc : (letE c : LetA O n) • w = w := inj _ _ (by
    rw [Relay2.mapA_smul, hw, smul_sub, hφXl, smul_comm (letE c : LetA O n) (lA W ^ A.σ PD.p), hxc])
  have hXΔ' := Relay2.Pp_Δ W Y c' A.j _ hX'
  have hwΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ w = w := fun δ hδ => inj _ _ (by
    rw [W.map_γ, hw, map_sub, PhiPowers.φD_pow_Δ W Y hXΔ' (A.len c - A.j) δ hδ, γD_lA, hxi.1.2 δ hδ])

  have e1 : W.map ι (W.γ T₂ w - w) = W.γ Y (W.map ι w) - W.map ι w := by rw [map_sub, hγι]
  have e2 : W.map ι (((W.φD T₂) ^ (A.len c - A.j)) (W.π₀ ^ A.M PD.p • m c') -
        lA W ^ A.σ PD.p • (W.π₀ • u' c)) =
      ((W.φD Y) ^ (A.len c - A.j)) (W.γ Y (Split.xsh W A ι x τ c') - Split.xsh W A ι x τ c') -
        lA W ^ A.σ PD.p • (W.γ Y (x c) - x c) := by
    rw [map_sub, Relay2.map_φpow, Relay2.mapA_smul W ι (lA W ^ A.σ PD.p), hu'x]
    congr 2
    exact hγX'.symm
  have e3 : W.γ Y (W.map ι w) - W.map ι w =
      ((W.φD Y) ^ (A.len c - A.j)) (W.γ Y (Split.xsh W A ι x τ c') - Split.xsh W A ι x τ c') -
        lA W ^ A.σ PD.p • (W.γ Y (x c) - x c) := by
    rw [hw, map_sub (W.γ Y), Split.γ_φpow, Relay2.γ_lsmul, map_sub ((W.φD Y) ^ (A.len c - A.j)), smul_sub]
    abel
  have hγw : W.γ T₂ w - w = ((W.φD T₂) ^ (A.len c - A.j)) (W.π₀ ^ A.M PD.p • m c') -
      lA W ^ A.σ PD.p • (W.π₀ • u' c) := inj _ _ (e1.trans (e3.trans e2.symm))
  obtain ⟨y'', hy''N, hy''⟩ := Split.InFN_φpow W T₂ (A.M PD.p) hq hF1a hmi'.1 (A.len c - A.j)
  have hml : (letE (c' + (A.j : ZMod n)) : LetA O n) • (W.π₀ ^ A.M PD.p • m c') =
      W.π₀ ^ A.M PD.p • m c' := by
    rw [smul_comm, Relay2.InNΔi_letter W T₂ _ hmi']
  have hφml := PhiPowers.φD_pow_letter W T₂ _ _ hml (A.len c - A.j)
  rw [hidx, hy''] at hφml
  have hy''c : (letE c : LetA O n) • y'' = y'' := by
    have h0 : W.π₀ ^ A.M PD.p • ((letE c : LetA O n) • y'' - y'') = 0 := by
      rw [smul_sub, smul_comm, hφml, sub_self]
    exact sub_eq_zero.1 (cancel_unit_mul_uniformizer_pow W hu T₂ _ h0)
  have hy''i : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c y'' := Relay2.InNΔi_of W T₂ c hy''N hy''c
  obtain ⟨M', hM'⟩ : ∃ M', A.M PD.p = M' + 1 := ⟨A.M PD.p - 1, by have := Relay2.M_pos A PD.p; omega⟩
  set z₀ : W.DD T₂ := W.π₀ ^ M' • y'' - lA W ^ A.σ PD.p • u' c with hz₀
  have hz₀i : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c z₀ :=
    Relay2.InNΔi_sub W T₂ c (Relay2.InNΔi_smul W T₂ c (W.AΔ.pow_mem hπ _) hy''i)
      (Relay2.InNΔi_lsmul W T₂ c _ hu'i)
  have hγw' : W.γ T₂ w - w = W.π₀ • z₀ := by
    rw [hγw, hy'', hM', hz₀]
    exact lin3 _ _ _ _ _ _
  have hIw : InI W T₂ c w := ⟨hwc, hwΔ, ⟨z₀, hz₀i.1, Relay2.InNΔi_letter W T₂ c hz₀i, hγw'⟩⟩

  have hΛ : abelian₂ W A c (A.len c) ∈ W.AΔ :=
    W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (PhiPowers.ps_mem_AΔ W hπ s) _
  have hAr := hArc hCA h5 A hA c hc (A.len c) hjl le_rfl
  dsimp only at hAr
  have hca : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  rw [hca] at hAr
  have hΛx : abelian₂ W A c (A.len c) • x c ∈ Pp W Y c' (A.len c) := by
    obtain ⟨y, hy, hyeq⟩ := (hAr.2 Y hWY).2.1 (x c) ⟨x c, hxi.1, hxc, (one_smul _ _).symm⟩
    rw [hyeq, one_smul]; exact hy
  have hφX : ((W.φD Y) ^ (A.len c - A.j)) (Split.xsh W A ι x τ c') ∈ Pp W Y c' (A.len c) := by
    have := Split.Pp_φpow W Y c' A.j (A.len c - A.j) hX'
    rwa [Nat.add_sub_cancel' hjl] at this
  have hιΛw : W.map ι (abelian₂ W A c (A.len c) • w) ∈ Pp W Y c' (A.len c) := by
    rw [Relay2.mapA_smul, hw, smul_sub, smul_comm (abelian₂ W A c (A.len c)) (lA W ^ A.σ PD.p)]
    exact (Pp W Y c' (A.len c)).sub_mem (Relay2.Pp_smul W Y c' _ hΛ _ hφX)
      (Relay2.Pp_smul W Y c' _ (W.AΔ.pow_mem (Relay2.lA_mem W) _) _ hΛx)
  have hPw : InFP W T₂ c' (A.len c) 1 (abelian₂ W A c (A.len c) • w) :=
    ⟨_, hpull c' hc' (A.len c) _ hιΛw, (one_smul _ _).symm⟩

  have hGw : Relay2.Good W T₂ c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) w (-(lA W ^ A.σ PD.p • τ c)) :=
    (Relay2.good_iff W T₂ c _ _ _ _ w _).2 (Relay2.goodZ_comb W T₂ c A.j _ _ _ hG hy''i (by rw [hγw, hy'']))
  have hτw : InFP W T₂ c A.j W.π₀ (-(lA W ^ A.σ PD.p • τ c)) :=
    Relay2.inMultiple_neg W T₂ c A.j _ (Relay2.inMultiple_lA_pow_smul W T₂ c A.j _ _ hτ)
  exact ⟨hIw, hPw, Relay2.mkTr W hinj hO2 h9 hH hTr hCA T₂ hT₂c A hM c ⟨z₀, hz₀i, hγw'⟩ hτw hGw⟩

/- English proof (translation)
Establish `h1 : IsUnit ((1 : ℤ_[l]) - (l : ℤ_[l]))` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ PadicInt.p_nonunit`. Establish `h2 : ((l - 1 : ℕ) : ℤ_[l]) = -((1 : ℤ_[l]) - (l : ℤ_[l]))`. Rewrite using `[Nat.cast_sub hl.out.one_le]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : IsUnit ((l - 1 : ℕ) : ℤ_[l])` using `by rw [h2]; exact h1.neg`. Simplify using `using h3.map (algebraMap ℤ_[l] ↥(OL LL))`.
-/
theorem isUnit_pred (l : ℕ) [hl : Fact l.Prime] (LL : FinExt l) : IsUnit ((l - 1 : ℕ) : ↥(OL LL)) := by
  have h1 : IsUnit ((1 : ℤ_[l]) - (l : ℤ_[l])) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ PadicInt.p_nonunit
  have h2 : ((l - 1 : ℕ) : ℤ_[l]) = -((1 : ℤ_[l]) - (l : ℤ_[l])) := by
    rw [Nat.cast_sub hl.out.one_le]; push_cast; ring
  have h3 : IsUnit ((l - 1 : ℕ) : ℤ_[l]) := by rw [h2]; exact h1.neg
  simpa using h3.map (algebraMap ℤ_[l] ↥(OL LL))

/- English proof (translation)
Take `⟨-, h9, -, hJ, -, hF1, hRel, hArc⟩` from `hAdm`. Introduce `l _ K LL hG hA h5`. Use `neZero_finrank_max_unramified K` as an intermediate fact. Establish `hone` using `Formalism.MainNotions.LiftingTheory.lone_HOne0_holds D HW F l K 1 LL hG`. Use `cutData_of _ Subtype.val_injective (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩) hone (fun hCA => ?_) (h9 l K 1 LL hG) (h6 l K 1 LL hG) (hH l K 1 LL hG) (hTr l K 1 LL hG) (hJ l K LL) (hF1 l K LL hG hA h5) (hRel l K LL hG hA h5) (hArc l K LL hG hA h5).1 (hX l K LL hG hA h5) …` and prove the remaining obligations.

Establish `hc` using `(h9 l K 1 LL hG _ hone.1 hCA.2.1 hCA.2.2).1`. Rewrite using `[hc, Formalism.MainNotions.LiftingTheory.frame_finrank_one _ hCA, Nat.div_one, (D.loc l).PD_p K]`. Conclude with `isUnit_pred l LL`.
-/
theorem cutDataL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hX : Split.DDExactL D HW) :
    Split.CutDataL D HW := by
  obtain ⟨-, h9, -, hJ, -, hF1, hRel, hArc⟩ := hAdm
  intro l _ K LL hG hA h5
  have := neZero_finrank_max_unramified K
  have hone := Formalism.MainNotions.LiftingTheory.lone_HOne0_holds D HW F l K 1 LL hG
  refine cutData_of _ Subtype.val_injective (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩)
    hone (fun hCA => ?_) (h9 l K 1 LL hG) (h6 l K 1 LL hG)
    (hH l K 1 LL hG) (hTr l K 1 LL hG) (hJ l K LL) (hF1 l K LL hG hA h5) (hRel l K LL hG hA h5)
    (hArc l K LL hG hA h5).1 (hX l K LL hG hA h5) (hWX l K 1 LL hG)
  have hc := (h9 l K 1 LL hG _ hone.1 hCA.2.1 hCA.2.2).1
  rw [hc, Formalism.MainNotions.LiftingTheory.frame_finrank_one _ hCA, Nat.div_one, (D.loc l).PD_p K]
  exact isUnit_pred l LL

end Formalism.MainNotions.UnusedSlot80.Split2

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
Unfold `SplittingTheoremArcLifting`. Introduce `hAdm`. Conclude with `splitting_of_exactness_and_data D HW F Cm hX (Split2.cutDataL_of D HW F Cm hAdm h6 hH hTr hWX hX) hS hAdm`.
-/
theorem splitting_of_lifting_chain (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hX : Split.DDExactL D HW)
    (hS : Split.SplitShapeL D HW) : SplittingTheoremArcLifting D HW F Cm := by
  unfold SplittingTheoremArcLifting
  intro hAdm
  exact splitting_of_exactness_and_data D HW F Cm hX (Split2.cutDataL_of D HW F Cm hAdm h6 hH hTr hWX hX) hS hAdm

/- English proof (translation)
Conclude with `splitting_of_lifting_chain D HW F Cm h6 hH hTr hWX hX hS hAdm`.
-/
theorem splitting_general_of_exactness (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hAdm : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F)
    (hX : Split.DDExactL D HW) (hS : Split.SplitShapeL D HW) : SplittingArcLifting D HW F Cm := by
  exact splitting_of_lifting_chain D HW F Cm h6 hH hTr hWX hX hS hAdm

end Formalism.MainNotions.UnusedSlot80
