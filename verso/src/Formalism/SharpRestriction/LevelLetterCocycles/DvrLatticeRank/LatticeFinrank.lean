import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SpanLeRange
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelQPfD
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GeneratorBoundOfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Formalism.MainNotions.N.Ln34.UniversalFiltration

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

/- English proof (translation)
Use `set bT := Module.Free.chooseBasis O T`. Use `set v : Module.Free.ChooseBasisIndex O T → V := fun i => (bT i : V)`. Establish `hli : LinearIndependent O v` using `bT.linearIndependent.map' T.subtype T.ker_subtype`. Establish `hliLL : LinearIndependent LL v` using `(LinearIndependent.iff_fractionRing O LL).1 hli`. Establish `hsp : Submodule.span LL (Set.range v) = ⊤`.

Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_le.2 fun x hx => ?_` and prove the remaining obligations. Establish `e : x = ∑ i, bT.repr ⟨x, hx⟩ i • v i` using `by conv_lhs => rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, ← bT.sum_repr ⟨x, hx⟩]`. Rewrite using `[Submodule.coe_sum]`. Both sides reduce to the same expression.

Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Module.finrank_eq_card_chooseBasisIndex, ← finrank_top LL V, ← hsp, finrank_span_eq_card hliLL]`.
-/
theorem lattice_finrank {O LL V : Type*} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL]
    [IsFractionRing O LL] [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    (T : Submodule O V) [Module.Free O T] [Module.Finite O T]
    (hspan : Submodule.span LL (T : Set V) = ⊤) : finrank O T = finrank LL V := by
  classical
  set bT := Module.Free.chooseBasis O T
  set v : Module.Free.ChooseBasisIndex O T → V := fun i => (bT i : V)
  have hli : LinearIndependent O v := bT.linearIndependent.map' T.subtype T.ker_subtype
  have hliLL : LinearIndependent LL v := (LinearIndependent.iff_fractionRing O LL).1 hli
  have hsp : Submodule.span LL (Set.range v) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine Submodule.span_le.2 fun x hx => ?_
    have e : x = ∑ i, bT.repr ⟨x, hx⟩ i • v i := by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : T) : V) from rfl, ← bT.sum_repr ⟨x, hx⟩]
      rw [Submodule.coe_sum]
      rfl
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [Module.finrank_eq_card_chooseBasisIndex, ← finrank_top LL V, ← hsp, finrank_span_eq_card hliLL]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `: IsFractionRing ↥(OL LL) ↥LL.1` using `GenPf.isFractionRing LL`. Use `set W := (HW l).W K 1 LL hG`. Establish `hs : W.s = 1` using `(HW l).W_s K 1 LL hG`. Establish `hp : ((D.loc l).PD K).p = l` using `(D.loc l).PD_p K`. Take `⟨-, ⟨-, -, -, ⟨r0, b, hbΔ, hbu, hbe⟩, -⟩, -⟩` from `(hA l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT hs (by rw [hp]; exact hl)`.

Take `⟨-, huniq, ⟨w₁, hw₁⟩, -⟩` from `hp9`. Establish `hl2 : 2 ≤ l` using `(Fact.out : l.Prime).two_le`. Establish `hd` using `Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG`. Establish `he : 0 < eK K` using `Nat.pos_of_ne_zero fun h0 => by`. Rewrite `hd` using `[h0, zero_dvd_iff]`.

Use linear arithmetic over natural numbers and integers. Establish `hsK : 1 ≤ sK l K` using `Nat.div_pos (Nat.le_of_dvd (by omega) hd) he`. Take `⟨bL0⟩` from `MQ.basis_L W T π' (sK l K) hsK w₁ hw₁ huniq b hbΔ hbu hbe c`. Establish `h1 : r = r0`. Establish `e1` using `Module.finrank_eq_card_basis bL`.

Establish `e2` using `Module.finrank_eq_card_basis bL0`. Simplify using `only [Fintype.card_fin] at e1 e2`. Use linear arithmetic over natural numbers and integers. Establish `hli : LinearIndependent (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (fun j => (⟨b j, (hbΔ j).1⟩ : W.N T))`. Use `Fintype.linearIndependent_iff.2 fun g hg => ?_` and prove the remaining obligations.

Establish `h1 : (∑ j, g j • b j) = 0`. Use `congrArg Subtype.val hg` as an intermediate fact. Simplify using `using this`. Take `⟨a0, _, hu⟩` from `hbu 0 (W.N T).zero_mem`. Establish `e1` using `hu g h1.symm`.

Establish `e2` using `hu 0 (by simp)`. Introduce `i`. Rewrite using `[e1, ← e2]`. Both sides reduce to the same expression. Establish `hsp : ⊤ ≤ Submodule.span (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (Set.range fun j => (⟨b j, (hbΔ j).1⟩ : W.N T))`.

Introduce and unpack `⟨x, hx⟩ _`. Take `⟨a, ha, _⟩` from `hbu x hx`. Establish `: (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hbΔ j).1⟩ : W.N T)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[ha]`.

Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Set `bN` to `Module.Basis.mk hli hsp`. Set `bD` to `IsBaseChange.basis bN (W.N_base T hT)`. Establish `: Nontrivial W.EE`.

Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h' : algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 0 = algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 1` using `by rw [map_zero, map_one]; exact h`. Establish `h0` using `congrFun (W.EE_inj h') 0`. Conclude with `zero_ne_one h0`. Establish `h2 : r0 = finrank W.EE (W.DD T)`.

Rewrite using `[Module.finrank_eq_card_basis bD, Fintype.card_fin]`. Establish `h3` using `(W.DD_free T).2`. Establish `: Module.Free ↥(OL LL) ↥T.L.T` using `T.L.free`. Establish `: Module.Finite ↥(OL LL) ↥T.L.T` using `Module.Finite.iff_fg.2 T.L.fg`. Rewrite using `[h1, h2, h3]`.

Conclude with `lattice_finrank T.L.T T.L.span`.
-/
theorem r_eq (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (r : ℕ)
    (bL : Basis (Fin r) ↥(OL LL) (LcQ ((HW l).W K 1 LL hG) T π' c)) : r = finrank ↥LL.1 T.V := by
  classical
  have : IsFractionRing ↥(OL LL) ↥LL.1 := GenPf.isFractionRing LL
  set W := (HW l).W K 1 LL hG
  have hs : W.s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨-, ⟨-, -, -, ⟨r0, b, hbΔ, hbu, hbe⟩, -⟩, -⟩ :=
    (hA l K 1 LL hG).2.2.2.2.2.2.2.2.1 T hT hs (by rw [hp]; exact hl)
  obtain ⟨-, huniq, ⟨w₁, hw₁⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  obtain ⟨bL0⟩ := MQ.basis_L W T π' (sK l K) hsK w₁ hw₁ huniq b hbΔ hbu hbe c
  have h1 : r = r0 := by
    have e1 := Module.finrank_eq_card_basis bL
    have e2 := Module.finrank_eq_card_basis bL0
    simp only [Fintype.card_fin] at e1 e2
    omega

  have hli : LinearIndependent (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    refine Fintype.linearIndependent_iff.2 fun g hg => ?_
    have h1 : (∑ j, g j • b j) = 0 := by
      have := congrArg Subtype.val hg
      simpa using this
    obtain ⟨a0, _, hu⟩ := hbu 0 (W.N T).zero_mem
    have e1 := hu g h1.symm
    have e2 := hu 0 (by simp)
    intro i
    rw [e1, ← e2]
    rfl
  have hsp : ⊤ ≤ Submodule.span (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (Set.range fun j => (⟨b j, (hbΔ j).1⟩ : W.N T)) := by
    rintro ⟨x, hx⟩ _
    obtain ⟨a, ha, _⟩ := hbu x hx
    have : (⟨x, hx⟩ : W.N T) = ∑ j, a j • (⟨b j, (hbΔ j).1⟩ : W.N T) := by
      apply Subtype.ext
      simp [ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := IsBaseChange.basis bN (W.N_base T hT)
  have : Nontrivial W.EE := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' : algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 0 =
        algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) W.EE 1 := by rw [map_zero, map_one]; exact h
    have h0 := congrFun (W.EE_inj h') 0
    exact zero_ne_one h0
  have h2 : r0 = finrank W.EE (W.DD T) := by
    rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]
  have h3 := (W.DD_free T).2
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  rw [h1, h2, h3]
  exact lattice_finrank T.L.T T.L.span

end Formalism.MainNotions.N.Ln34.UniversalFiltration

end
