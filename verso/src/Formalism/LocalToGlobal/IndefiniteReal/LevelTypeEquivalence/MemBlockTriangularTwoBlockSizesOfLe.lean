import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PrincipalLevelAction
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqAct

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Eqv.Act

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Links.RealDat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)}

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem choose_congr' {α : Type*} {p q : α → Prop} (hp : ∃ x, p x) (hq : ∃ x, q x) (e : p = q) :
    hp.choose = hq.choose := by
  subst e; rfl

/- English proof (translation)
Use function extensionality and compare the values at `F`. Unfold `actG0`. Distinguish the cases in `h : ∃ κ, IsLevelLift V β L1 g1 κ`. Establish `h' : ∃ κ, IsLevelLift V β L2 g2 κ` using `let ⟨κ, hκ⟩ := h`. Use the proof step `⟨κ, (hI κ).1 hκ⟩`.

Rewrite using `[dif_pos h, dif_pos h', choose_congr' h h' (funext fun κ => propext (hI κ))]`. Simplify using `only [hc]`. Establish `h' : ¬ ∃ κ, IsLevelLift V β L2 g2 κ` using `fun ⟨κ, hκ⟩ => h ⟨κ, (hI κ).2 hκ⟩`. Rewrite using `[dif_neg h, dif_neg h']`.
-/
theorem level_action_congr {L1 L2 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (g1 : Formalism.L2.DIV.G0 L1.Pg L1.r)
    (g2 : Formalism.L2.DIV.G0 L2.Pg L2.r) (hI : ∀ κ, IsLevelLift V β L1 g1 κ ↔ IsLevelLift V β L2 g2 κ)
    (hc : ∀ κ, levChi V β (flagL L1) κ = levChi V β (flagL L2) κ) :
    actG0 V β L1 g1 = actG0 V β L2 g2 := by
  funext F
  unfold actG0
  by_cases h : ∃ κ, IsLevelLift V β L1 g1 κ
  · have h' : ∃ κ, IsLevelLift V β L2 g2 κ := let ⟨κ, hκ⟩ := h; ⟨κ, (hI κ).1 hκ⟩
    rw [dif_pos h, dif_pos h', choose_congr' h h' (funext fun κ => propext (hI κ))]
    simp only [hc]
  · have h' : ¬ ∃ κ, IsLevelLift V β L2 g2 κ := fun ⟨κ, hκ⟩ => h ⟨κ, (hI κ).2 hκ⟩
    rw [dif_neg h, dif_neg h']

variable {n r : ℕ} {κF : Type} [CommRing κF]

/- English proof (translation)
Use `show (g : Matrix (Fin n) (Fin n) κF).BlockTriangular (blk2 r)`. Introduce `i j hij`. Establish `hi : i.val < r` using `lt_of_lt_of_le i.2 hn`. Establish `hj : j.val < r` using `lt_of_lt_of_le j.2 hn`. Simplify using `[blk2, hi, hj] at hij`.
-/
theorem mem_blockTriangular_twoBlockSizes_of_le {r : ℕ} (hn : n ≤ r) (g : GL (Fin n) κF) : g ∈ blockTri (blk2 (n := n) r) := by
  show (g : Matrix (Fin n) (Fin n) κF).BlockTriangular (blk2 r)
  intro i j hij
  have hi : i.val < r := lt_of_lt_of_le i.2 hn
  have hj : j.val < r := lt_of_lt_of_le j.2 hn
  simp [blk2, hi, hj] at hij

/- English proof (translation)
Unfold `dBlk`. Rewrite using `[extendOne_of_mem _ (mem_blockTriangular_twoBlockSizes_of_le hn g)]`. Establish `: IsEmpty {a : Fin n // blk2 r a = 1}` using `⟨fun a => by`. Establish `ha` using `a.2`. Simplify using `[blk2, lt_of_lt_of_le a.1.2 hn] at ha⟩`.

Use `ext`. Simplify using `[blkDet]`.
-/
theorem block_determinant_empty_eq_one {r : ℕ} (hn : n ≤ r) (g : GL (Fin n) κF) : dBlk (blk2 (n := n) r) 1 g = 1 := by
  unfold dBlk
  rw [extendOne_of_mem _ (mem_blockTriangular_twoBlockSizes_of_le hn g)]
  have : IsEmpty {a : Fin n // blk2 r a = 1} :=
    ⟨fun a => by
      have ha := a.2
      simp [blk2, lt_of_lt_of_le a.1.2 hn] at ha⟩
  ext
  simp [blkDet]

/- English proof (translation)
Unfold `parLev`. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, -⟩`. Use `⟨h1, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩` and prove the remaining obligations.

Introduce and unpack `⟨h1, -⟩`. Use `⟨h1, fun PP _ => ?_⟩` and prove the remaining obligations. Establish `hst : x ∈ St β` using `h1.1.2`. Conclude with `mem_parah.2 ⟨hst, mem_blockTriangular_twoBlockSizes_of_le (n := V.rank) (κF := kP PP) hn (redFn β PP x)⟩`.
-/
theorem mem_parLev_datY_noQ (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (x : GL (Fin V.rank) (EAf D)) :
    x ∈ parLev D.sp.cm V.gram β (datY V.rank r t j hr Pg Q P χ ξ fr) ↔
      x ∈ parLev D.sp.cm V.gram β (datY V.rank r t j hr Pg ∅ P χ ξ' fr) := by
  unfold parLev
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · rintro ⟨h1, -⟩
    refine ⟨h1, fun PP hPP => absurd hPP (Finset.notMem_empty _)⟩
  · rintro ⟨h1, -⟩
    refine ⟨h1, fun PP _ => ?_⟩
    have hst : x ∈ St β := h1.1.2
    exact mem_parah.2 ⟨hst, mem_blockTriangular_twoBlockSizes_of_le (n := V.rank) (κF := kP PP) hn (redFn β PP x)⟩

/- English proof (translation)
Unfold `levFn`. Establish `hq : ∀ PP ∈ (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).Q, (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).xq PP (dBlk (blk2 (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r) 1 (redFn β PP x)) = 1`. Introduce `PP _`. Use `show _ = 1`. Rewrite using `[show (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r = r from rfl, block_determinant_empty_eq_one hn, map_one]`.

Rewrite using `[Finset.prod_eq_one hq]`. Both sides reduce to the same expression.
-/
theorem levFn_datY_noQ (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (x : GL (Fin V.rank) (EAf D)) :
    levFn β (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)) x = levFn β (flagL (datY V.rank r t j hr Pg ∅ P χ ξ' fr)) x := by
  unfold levFn
  have hq : ∀ PP ∈ (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).Q,
      (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).xq PP
        (dBlk (blk2 (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r) 1 (redFn β PP x)) = 1 := by
    intro PP _
    show _ = 1
    rw [show (flagL (datY V.rank r t j hr Pg Q P χ ξ fr)).r = r from rfl, block_determinant_empty_eq_one hn, map_one]
  rw [Finset.prod_eq_one hq]
  rfl

/- English proof (translation)
Use `level_action_congr (L1 := datY V.rank r t j hr Pg Q P χ ξ fr) (L2 := datY V.rank r t j hr Pg ∅ P χ ξ' fr) g0 g0 (fun κ => ?_) (fun κ => ?_)` and prove the remaining obligations. Unfold `IsLevelLift`. Rewrite using `[mem_parLev_datY_noQ hn hr t j Pg Q P χ ξ ξ' fr]`. Both sides reduce to the same expression. Unfold `levChi`.

Rewrite using `[levFn_datY_noQ hn hr t j Pg Q P χ ξ ξ' fr]`.
-/
theorem level_action_independent_of_primes (hn : V.rank ≤ r) (hr : r ≤ V.rank) (t j : ℕ) (Pg Q : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (fr : Formalism.IndefR.Lev.Frm)
    (g0 : G0 Pg r) :
    actG0 V β (datY V.rank r t j hr Pg Q P χ ξ fr) g0 = actG0 V β (datY V.rank r t j hr Pg ∅ P χ ξ' fr) g0 := by
  refine level_action_congr (L1 := datY V.rank r t j hr Pg Q P χ ξ fr) (L2 := datY V.rank r t j hr Pg ∅ P χ ξ' fr) g0 g0
    (fun κ => ?_) (fun κ => ?_)
  · unfold IsLevelLift
    rw [mem_parLev_datY_noQ hn hr t j Pg Q P χ ξ ξ' fr]
    rfl
  · unfold levChi
    rw [levFn_datY_noQ hn hr t j Pg Q P χ ξ ξ' fr]

end Gen

section Idem

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Simplify using `[chiIdem, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]`.
-/
theorem chiIdem_coeff' (χ : G → K) (t : G) :
    (chiIdem χ).coeff t = χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  classical
  simp [chiIdem, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/- English proof (translation)
Simplify using `[idemOf, MonoidAlgebra.coeff_sum, chiIdem_coeff']`.
-/
theorem idemOf_coeff' (X : Finset (G → K)) (t : G) :
    (idemOf X).coeff t = ∑ χ ∈ X, χ 1 / (Fintype.card G : K) * χ t⁻¹ := by
  simp [idemOf, MonoidAlgebra.coeff_sum, chiIdem_coeff']

/- English proof (translation)
Take `⟨n, ρ, -, hρ⟩` from `h`. Apply `(algebraMap K (AlgebraicClosure K)).injective` to reduce the goal to its premises. Rewrite using `[← hρ, ← hρ, Representation.char_conj]`.
-/
theorem isAbsIrrChar_conj {χ : G → K} (h : IsAbsIrrChar χ) (g t : G) : χ (g * t * g⁻¹) = χ t := by
  obtain ⟨n, ρ, -, hρ⟩ := h
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [← hρ, ← hρ, Representation.char_conj]

/- English proof (translation)
Rewrite using `[idemOf_coeff', idemOf_coeff']`. Use `Finset.sum_congr rfl fun χ hχ => ?_` and prove the remaining obligations. Establish `: (g * t * g⁻¹)⁻¹ = g * t⁻¹ * g⁻¹` using `by group`. Rewrite using `[this, isAbsIrrChar_conj (hX χ hχ)]`.
-/
theorem idemOf_coeff_conj (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (g t : G) :
    (idemOf X).coeff (g * t * g⁻¹) = (idemOf X).coeff t := by
  rw [idemOf_coeff', idemOf_coeff']
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have : (g * t * g⁻¹)⁻¹ = g * t⁻¹ * g⁻¹ := by group
  rw [this, isAbsIrrChar_conj (hX χ hχ)]

end Idem

section GA

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

/- English proof (translation)
Establish `e : ∀ F' : GA D V → ℂ, gaL V β L eG c F' = ∑ h, c h • actG0 V β L (eG h) F'` using `fun F' => by`. Simplify using `[gaL, actL]`. Rewrite using `[e, e]`. Use `show ∑ h, c h • actG0 V β L (eG h) (actG0 V β L (eG g) F) = actG0 V β L (eG g) (∑ h, c h • actG0 V β L (eG h) F)`. Establish `e2 : actG0 V β L (eG g) (∑ h, c h • actG0 V β L (eG h) F) = ∑ h, c h • actG0 V β L (eG g) (actG0 V β L (eG h) F)` using `by show actL V β L (eG g) (∑ h, c h • actL V β L (eG h) F) = ∑ h, c h • actL V β L (eG g) (actL V β L (eG h) F)`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul]`. Rewrite using `[e2]`. Use `Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ fun h => ?_` and prove the remaining obligations.

Use `show c h • actG0 V β L (eG h) (actG0 V β L (eG g) F) = c (g⁻¹ * h * g⁻¹⁻¹) • actG0 V β L (eG g) (actG0 V β L (eG (g⁻¹ * h * g⁻¹⁻¹)) F)`. Rewrite using `[inv_inv]`. Rewrite using `[levelGroupAction_mul_of_lifts hL (eG h) (eG g) hF, levelGroupAction_mul_of_lifts hL (eG g) (eG (g⁻¹ * h * g)) hF, ← map_mul, ← map_mul]`. Establish `e3 : c (g⁻¹ * h * g) = c h` using `by simpa using hc g⁻¹ h`. Rewrite using `[e3, show g * (g⁻¹ * h * g) = h * g by group]`.
-/
theorem gaL_comm {G : Type} [Group G] [Fintype G] (hL : LiftsExist V β L) (eG : G ≃* Formalism.L2.DIV.G0 L.Pg L.r)
    (c : G → ℂ) (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : G) {F : GA D V → ℂ} (hF : HasType V β (flag1L L) F) :
    gaL V β L eG c (actL V β L (eG g) F) = actL V β L (eG g) (gaL V β L eG c F) := by
  have e : ∀ F' : GA D V → ℂ, gaL V β L eG c F' = ∑ h, c h • actG0 V β L (eG h) F' := fun F' => by
    simp [gaL, actL]
  rw [e, e]
  show ∑ h, c h • actG0 V β L (eG h) (actG0 V β L (eG g) F) =
    actG0 V β L (eG g) (∑ h, c h • actG0 V β L (eG h) F)
  have e2 : actG0 V β L (eG g) (∑ h, c h • actG0 V β L (eG h) F) =
      ∑ h, c h • actG0 V β L (eG g) (actG0 V β L (eG h) F) := by
    show actL V β L (eG g) (∑ h, c h • actL V β L (eG h) F) = ∑ h, c h • actL V β L (eG g) (actL V β L (eG h) F)
    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [LinearMap.map_smul]
  rw [e2]
  refine Fintype.sum_equiv (MulAut.conj g⁻¹).toEquiv _ _ fun h => ?_
  show c h • actG0 V β L (eG h) (actG0 V β L (eG g) F) =
    c (g⁻¹ * h * g⁻¹⁻¹) • actG0 V β L (eG g) (actG0 V β L (eG (g⁻¹ * h * g⁻¹⁻¹)) F)
  rw [inv_inv]
  rw [levelGroupAction_mul_of_lifts hL (eG h) (eG g) hF, levelGroupAction_mul_of_lifts hL (eG g) (eG (g⁻¹ * h * g)) hF, ← map_mul, ← map_mul]
  have e3 : c (g⁻¹ * h * g) = c h := by simpa using hc g⁻¹ h
  rw [e3, show g * (g⁻¹ * h * g) = h * g by group]

end GA

section MultLev

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

/- English proof (translation)
Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem x hx => exact hx.lev`. Consider the case `zero => intro v k _ g`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy => intro v k hk g`.

Simplify using `[hx v k hk g, hy v k hk g, mul_add]`. Consider the case `smul a x _ hx => intro v k hk g`. Simplify using `[hx v k hk g, mul_left_comm]`.
-/
theorem mult_lev' {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {T : MMap M} (hT : T ∈ Mult θ M J χ) : ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intro v k _ g; simp
  | add x y _ _ hx hy => intro v k hk g; simp [hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx => intro v k hk g; simp [hx v k hk g, mul_left_comm]

end MultLev

section Real

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

/- English proof (translation)
Rewrite using `[D.sp.Y_rank _ (min_le_right _ _)]`. Use `show D.R.r + min 0 D.R.m * D.R.t ≤ D.R.r`. Simplify using the standard rewrite rules.
-/
theorem rank_lowerChainSpace_zero_le : (Yc D 0).rank ≤ D.R.r := by
  rw [D.sp.Y_rank _ (min_le_right _ _)]
  show D.R.r + min 0 D.R.m * D.R.t ≤ D.R.r
  simp

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Use `show actG0 (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) (R.eG g) F = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) F`. Unfold `LevCh.datYt LevCh.dat0`. Rewrite using `[level_action_independent_of_primes rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Frm.B]`.
-/
theorem actYt_zero (t : T) (g : G) : actYt R t 0 g = principalLevelAction R g := by
  refine LinearMap.ext fun F => ?_
  show actG0 (Yc D 0) (R.βY 0) (R.datYt t 0 R.triv) (R.eG g) F = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) F
  unfold LevCh.datYt LevCh.dat0
  rw [level_action_independent_of_primes rank_lowerChainSpace_zero_le (r_le_Y 0) D.R.t 0 R.Pg (R.Q t) R.triv R.chi (R.xiR t) (fun _ => 1) Frm.B]

end Real

end Formalism.IndefR.Eqv.Act

end
