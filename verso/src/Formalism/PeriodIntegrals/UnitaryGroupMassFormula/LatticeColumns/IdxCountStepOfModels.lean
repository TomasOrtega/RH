import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.HBlock
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxDone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ParabolicReductionImage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.GlRedEqOneIff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets Formalism.L2.SG.Measures Formalism.L2.SG.Sub
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Formalism.FourierDecayAlt.S3
open scoped Matrix

variable {D : D7}

def HModelU (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X) : Prop :=
  ∃ (ψ : KvA X p.1 →* GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) (c : GL (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p))
    (π : MassDataIdxSteps.Op X p →+* ZMod (gOf p)) (d : GL (Fin D.R.k) (ZMod (gOf p))),
    Function.Surjective ψ ∧
    (∀ x : KvA X p.1, (∀ i j, ((ψ x : Matrix (Idx D.R.rS D.R.k) (Idx D.R.rS D.R.k) (MassDataIdxSteps.Op X p)) - 1) i j ∈
      Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)}) ↔ (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ MassDataIdxSteps.KgX X p) ∧
    (∀ x : KvA X p.1, (x : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) ↔
      c⁻¹ * ψ x * c ∈ (hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k).range) ∧
    Function.Surjective π ∧ RingHom.ker π = Ideal.span {((gOf p : ℕ) : MassDataIdxSteps.Op X p)} ∧
    ∀ (x : KvH X u p.1) (B : GL (Fin D.R.k) (MassDataIdxSteps.Op X p)),
      c⁻¹ * ψ (inclH X u p x) * c = hEmbGL D.R.rS D.R.k B →
      (x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
        d⁻¹ * MassDataIdxRed.glRed π B * d ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k)

/- English proof (translation)
Take `⟨ψ, c, _π, _d, hψ, hker, hH, _⟩` from `h`. Conclude with `⟨ψ, c, hψ, hker, hH⟩`.
-/
theorem hModel_of_U (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word) (p : TypX X)
    (h : HModelU X hb u p) : HModel X u p := by
  obtain ⟨ψ, c, _π, _d, hψ, hker, hH, _⟩ := h
  exact ⟨ψ, c, hψ, hker, hH⟩

/- English proof (translation)
Use extensionality with `i j`. Use `congrArg (fun g : GL (Idx r k) A => (g : Matrix (Idx r k) (Idx r k) A) (Sum.inr (Sum.inl (Sum.inl i))) (Sum.inr (Sum.inl (Sum.inl j)))) h` as an intermediate fact. Express the relevant statement in the definitionally equal form `hEmb r (B : Matrix (Fin k) (Fin k) A) _ _ = hEmb r (B' : Matrix (Fin k) (Fin k) A) _ _ at this`. Simplify `this` using `[hEmb, midEmb]`.
-/
private theorem hEmbGL_inj {A : Type} [CommRing A] (r k : ℕ) {B B' : GL (Fin k) A}
    (h : hEmbGL (A := A) r k B = hEmbGL (A := A) r k B') : B = B' := by
  ext i j
  have := congrArg (fun g : GL (Idx r k) A => (g : Matrix (Idx r k) (Idx r k) A)
    (Sum.inr (Sum.inl (Sum.inl i))) (Sum.inr (Sum.inl (Sum.inl j)))) h
  change hEmb r (B : Matrix (Fin k) (Fin k) A) _ _ = hEmb r (B' : Matrix (Fin k) (Fin k) A) _ _ at this
  simpa [hEmb, midEmb] using this

/- English proof (translation)
Rewrite using `[Units.ext_iff, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `π ((g : Matrix ι ι R) i j) = (1 : Matrix ι ι S) i j ↔ _`. Rewrite using `[RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero]`. Simplify using `only [Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem glRed_eq_one_iff_sub_one_mem_ker {ι R S : Type} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing S]
    (π : R →+* S) (g : GL ι R) :
    MassDataIdxRed.glRed π g = 1 ↔ ∀ i j, ((g : Matrix ι ι R) - 1) i j ∈ RingHom.ker π := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change π ((g : Matrix ι ι R) i j) = (1 : Matrix ι ι S) i j ↔ _
  rw [RingHom.mem_ker, Matrix.sub_apply, map_sub, sub_eq_zero]
  simp only [Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(hEmb r (B : Matrix (Fin k) (Fin k) R)).map π = hEmb r ((B : Matrix (Fin k) (Fin k) R).map π)`. Simplify using `[hEmb, midEmb, Matrix.fromBlocks_map, Matrix.map_one, Matrix.map_zero]`.
-/
private theorem glRed_hEmbGL {R S : Type} [CommRing R] [CommRing S] (π : R →+* S) (r k : ℕ)
    (B : GL (Fin k) R) :
    MassDataIdxRed.glRed π (hEmbGL (A := R) r k B) = hEmbGL (A := S) r k (MassDataIdxRed.glRed π B) := by
  apply Units.ext
  change (hEmb r (B : Matrix (Fin k) (Fin k) R)).map π = hEmb r ((B : Matrix (Fin k) (Fin k) R).map π)
  simp [hEmb, midEmb, Matrix.fromBlocks_map, Matrix.map_one, Matrix.map_zero]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨ψ, c, π, d, hψ, hker, hH, hπ, hπker, hK2⟩` from `h`. Introduce `ρ hρ hρker`. Establish `hconj : ∀ {G : Type} [Group G] (a b : G), a⁻¹ * b * a = 1 ↔ b = 1`. Introduce `G _ a b`. Prove the components needed by the constructor for the conclusion.

Introduce `h'`. Combine the equalities or inequalities in the displayed calculation. Introduce `h'`. Rewrite using `[h']`. Use `group`.

Establish `hmem : ∀ x : KvH X u p.1, ∃ B, hEmbGL (A` using `MassDataIdxSteps.Op X p) D.R.rS D.R.k B = c⁻¹ * ψ (inclH X u p x) * c := fun x => MonoidHom.mem_range.1 ((hH (inclH X u p x)).1 (x.1).2)`. Use `choose B hB using hmem`. Take `⟨β, hβ⟩ : ∃ β : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p), ∀ x, hEmbGL (A` from `MassDataIdxSteps.Op X p) D.R.rS D.R.k (β x) = c⁻¹ * ψ (inclH X u p x) * c := ⟨MonoidHom.mk' B (fun x y => hEmbGL_inj D.R.rS D.R.k (by`. Simplify using `only [map_mul, hB]`. Use the proof step `group)), hB⟩`.

Take `⟨σ, hσ⟩ : ∃ σ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)), ∀ x, σ x = MassDataIdxRed.glRed π (β x)` from `⟨(MassDataIdxRed.glRed π).comp β, fun _ => rfl⟩`. Establish `hS : ∀ x, x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔ d⁻¹ * σ x * d ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k`. Introduce `x`. Rewrite using `[hσ]`. Conclude with `hK2 x (β x) (hβ x).symm`.

Establish `e2 : ∀ z : GL (Fin D.R.k) (ZMod (gOf p)), hEmbGL (A` using `ZMod (gOf p)) D.R.rS D.R.k z = 1 ↔ z = 1 := fun z => ⟨fun h' => hEmbGL_inj D.R.rS D.R.k (h'.trans (map_one _).symm), fun h' => by rw [h', map_one]⟩`. Establish `hσker : ∀ x, σ x = 1 ↔ x ∈ KgH X u p`. Introduce `x`. Establish `e1 : MassDataIdxRed.glRed π (ψ (inclH X u p x)) = 1 ↔ x ∈ KgH X u p`. Rewrite using `[glRed_eq_one_iff_sub_one_mem_ker, hπker]`.

Conclude with `hker (inclH X u p x)`. Rewrite using `[← e1, hσ]`. Conclude with `(e2 _).symm.trans (by`. Rewrite using `[← glRed_hEmbGL, hβ x, map_mul, map_mul, map_inv, hconj])`. Establish `hgl : Function.Surjective (MassDataIdxRed.glRed (ι` using `Fin D.R.k) π) := by`.

Distinguish the cases in `hs : Subsingleton (ZMod (gOf p))`. Introduce `z`. Conclude with `⟨1, Units.ext (Matrix.ext fun i j => @Subsingleton.elim _ hs _ _)⟩`. Use `MassDataIdxRed.glRed_surjective π hπ ?_` and prove the remaining obligations. Introduce `r hr`.

Assume the negation of the conclusion as `hnu`. Apply `hs` to reduce the goal to its premises. Take `⟨s, hs'⟩` from `hr.exists_right_inv`. Take `⟨t, rfl⟩` from `hπ s`. Establish `hm : r * t ∈ nonunits (MassDataIdxSteps.Op X p)` using `mem_nonunits_iff.2 fun h' => hnu (isUnit_of_mul_isUnit_left h')`.

Establish `hu` using `IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm`. Establish `h0 : π (1 - r * t) = 0` using `by rw [map_sub, map_one, map_mul, hs', sub_self]`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `h1` using `congrArg π hw`. Rewrite `h1` using `[map_mul, h0, zero_mul, map_one]`.

Conclude with `subsingleton_of_zero_eq_one h1`. Establish `hβs : Function.Surjective β`. Introduce `Bz`. Take `⟨y, hy⟩` from `hψ (c * hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k Bz * c⁻¹)`. Establish `hyH : (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u)` using `(hH y).2 (MonoidHom.mem_range.2 ⟨Bz, by rw [hy]; group⟩)`.

Use `⟨⟨⟨(y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J), hyH⟩, y.2⟩, ?_⟩` and prove the remaining obligations. Apply `hEmbGL_inj D.R.rS D.R.k` to reduce the goal to its premises. Rewrite using `[hβ]`. Use `show c⁻¹ * ψ y * c = hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k Bz`. Rewrite using `[hy]`.

Use `group`. Establish `hσs : Function.Surjective σ`. Introduce `z`. Take `⟨Bz, rfl⟩` from `hgl z`. Take `⟨x, rfl⟩` from `hβs Bz`.

Conclude with `⟨x, hσ x⟩`. Establish `hkerEq : σ.ker = ρ.ker`. Use extensionality with `x`. Conclude with `MonoidHom.mem_ker.trans ((hσker x).trans ((hρker x).symm.trans MonoidHom.mem_ker.symm))`. Set `eσ` to `QuotientGroup.quotientKerEquivOfSurjective σ hσs`.

Set `eρ` to `QuotientGroup.quotientKerEquivOfSurjective ρ hρ`. Choose the witnesses or unpack the hypotheses as in `⟨α, hα⟩ : ∃ α : GL (Fin D.R.k) (ZMod (gOf p)) ≃* GL (Fin D.R.k) (ZMod (gOf p)), ∀ x, α (σ x) = ρ x := by`. Use `⟨(eσ.symm.trans (QuotientGroup.quotientMulEquivOfEq hkerEq)).trans eρ, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : eσ.symm (σ x) = (x : ↥(KvH X u p.1) ⧸ σ.ker)`. Rewrite using `[MulEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Rewrite using `[MulEquiv.trans_apply, MulEquiv.trans_apply, h1]`. Both sides reduce to the same expression. Establish `hmap : ((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ = ((Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k).map (MulAut.conj d).toMonoidHom).map α.toMonoidHom`. Use extensionality with `z`.

Simplify using `only [Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Use `⟨σ x, ⟨d⁻¹ * σ x * d, (hS x).1 hx, ?_⟩, hα x⟩` and prove the remaining obligations. Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`.

Use `group`. Introduce and unpack `⟨w, ⟨v, hv, rfl⟩, rfl⟩`. Take `⟨x, hx⟩` from `hσs ((MulAut.conj d).toMonoidHom v)`. Use `⟨x, (hS x).2 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`.

Simplify using `only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Establish `hdv : d⁻¹ * (d * v * d⁻¹) * d = v` using `by group`. Rewrite using `[hdv]`. Conclude with `hv`. Rewrite using `[← hα x, hx]`.

Both sides reduce to the same expression. Rewrite using `[hmap, Subgroup.card_map_of_injective (show Function.Injective α.toMonoidHom from α.injective), Subgroup.card_map_of_injective (show Function.Injective (MulAut.conj d).toMonoidHom from (MulAut.conj d).injective)]`. Both sides reduce to the same expression.
-/
theorem hImU_of_model (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (hL : X.LevelSubgroupNormalized)
    (u : D.what₂.Word) (p : TypX X) (h : HModelU X hb u p) : HImU X hb u p := by
  obtain ⟨ψ, c, π, d, hψ, hker, hH, hπ, hπker, hK2⟩ := h
  intro ρ hρ hρker
  have hconj : ∀ {G : Type} [Group G] (a b : G), a⁻¹ * b * a = 1 ↔ b = 1 := by
    intro G _ a b
    constructor
    · intro h'
      calc b = a * (a⁻¹ * b * a) * a⁻¹ := by group
        _ = 1 := by rw [h']; group
    · intro h'
      rw [h']; group
  have hmem : ∀ x : KvH X u p.1, ∃ B, hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k B =
      c⁻¹ * ψ (inclH X u p x) * c :=
    fun x => MonoidHom.mem_range.1 ((hH (inclH X u p x)).1 (x.1).2)
  choose B hB using hmem
  obtain ⟨β, hβ⟩ : ∃ β : KvH X u p.1 →* GL (Fin D.R.k) (MassDataIdxSteps.Op X p),
      ∀ x, hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k (β x) = c⁻¹ * ψ (inclH X u p x) * c :=
    ⟨MonoidHom.mk' B (fun x y => hEmbGL_inj D.R.rS D.R.k (by
      simp only [map_mul, hB]
      group)), hB⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : KvH X u p.1 →* GL (Fin D.R.k) (ZMod (gOf p)),
      ∀ x, σ x = MassDataIdxRed.glRed π (β x) := ⟨(MassDataIdxRed.glRed π).comp β, fun _ => rfl⟩
  have hS : ∀ x, x ∈ (unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1) ↔
      d⁻¹ * σ x * d ∈ Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k := by
    intro x
    rw [hσ]
    exact hK2 x (β x) (hβ x).symm
  have e2 : ∀ z : GL (Fin D.R.k) (ZMod (gOf p)),
      hEmbGL (A := ZMod (gOf p)) D.R.rS D.R.k z = 1 ↔ z = 1 := fun z =>
    ⟨fun h' => hEmbGL_inj D.R.rS D.R.k (h'.trans (map_one _).symm), fun h' => by rw [h', map_one]⟩
  have hσker : ∀ x, σ x = 1 ↔ x ∈ KgH X u p := by
    intro x
    have e1 : MassDataIdxRed.glRed π (ψ (inclH X u p x)) = 1 ↔ x ∈ KgH X u p := by
      rw [glRed_eq_one_iff_sub_one_mem_ker, hπker]
      exact hker (inclH X u p x)
    rw [← e1, hσ]
    exact (e2 _).symm.trans (by
      rw [← glRed_hEmbGL, hβ x, map_mul, map_mul, map_inv, hconj])
  have hgl : Function.Surjective (MassDataIdxRed.glRed (ι := Fin D.R.k) π) := by
    by_cases hs : Subsingleton (ZMod (gOf p))
    · intro z
      exact ⟨1, Units.ext (Matrix.ext fun i j => @Subsingleton.elim _ hs _ _)⟩
    · refine MassDataIdxRed.glRed_surjective π hπ ?_
      intro r hr
      by_contra hnu
      apply hs
      obtain ⟨s, hs'⟩ := hr.exists_right_inv
      obtain ⟨t, rfl⟩ := hπ s
      have hm : r * t ∈ nonunits (MassDataIdxSteps.Op X p) :=
        mem_nonunits_iff.2 fun h' => hnu (isUnit_of_mul_isUnit_left h')
      have hu := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
      have h0 : π (1 - r * t) = 0 := by rw [map_sub, map_one, map_mul, hs', sub_self]
      obtain ⟨w, hw⟩ := hu.exists_right_inv
      have h1 := congrArg π hw
      rw [map_mul, h0, zero_mul, map_one] at h1
      exact subsingleton_of_zero_eq_one h1
  have hβs : Function.Surjective β := by
    intro Bz
    obtain ⟨y, hy⟩ := hψ (c * hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k Bz * c⁻¹)
    have hyH : (y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) ∈
        Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X u) :=
      (hH y).2 (MonoidHom.mem_range.2 ⟨Bz, by rw [hy]; group⟩)
    refine ⟨⟨⟨(y : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J), hyH⟩, y.2⟩, ?_⟩
    apply hEmbGL_inj D.R.rS D.R.k
    rw [hβ]
    show c⁻¹ * ψ y * c = hEmbGL (A := MassDataIdxSteps.Op X p) D.R.rS D.R.k Bz
    rw [hy]
    group
  have hσs : Function.Surjective σ := by
    intro z
    obtain ⟨Bz, rfl⟩ := hgl z
    obtain ⟨x, rfl⟩ := hβs Bz
    exact ⟨x, hσ x⟩
  have hkerEq : σ.ker = ρ.ker := by
    ext x
    exact MonoidHom.mem_ker.trans ((hσker x).trans ((hρker x).symm.trans MonoidHom.mem_ker.symm))
  let eσ := QuotientGroup.quotientKerEquivOfSurjective σ hσs
  let eρ := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  obtain ⟨α, hα⟩ : ∃ α : GL (Fin D.R.k) (ZMod (gOf p)) ≃* GL (Fin D.R.k) (ZMod (gOf p)),
      ∀ x, α (σ x) = ρ x := by
    refine ⟨(eσ.symm.trans (QuotientGroup.quotientMulEquivOfEq hkerEq)).trans eρ, fun x => ?_⟩
    have h1 : eσ.symm (σ x) = (x : ↥(KvH X u p.1) ⧸ σ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  have hmap : ((unitaryLevelLocalComponent X hb u p.1).subgroupOf (KvH X u p.1)).map ρ =
      ((Formalism.DoubleCosetMeasures.upUniG (ZMod (gOf p)) D.R.k).map (MulAut.conj d).toMonoidHom).map α.toMonoidHom := by
    ext z
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨σ x, ⟨d⁻¹ * σ x * d, (hS x).1 hx, ?_⟩, hα x⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      obtain ⟨x, hx⟩ := hσs ((MulAut.conj d).toMonoidHom v)
      refine ⟨x, (hS x).2 ?_, ?_⟩
      · rw [hx]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have hdv : d⁻¹ * (d * v * d⁻¹) * d = v := by group
        rw [hdv]
        exact hv
      · rw [← hα x, hx]
        rfl
  rw [hmap, Subgroup.card_map_of_injective (show Function.Injective α.toMonoidHom from α.injective),
    Subgroup.card_map_of_injective (show Function.Injective (MulAut.conj d).toMonoidHom from
      (MulAut.conj d).injective)]
  rfl

/- English proof (translation)
Introduce `D X hb hK u hM hL p`. Establish `hm` using `h X hb hK u hM hL p`. Use `⟨?_, hLatGL_of_model X u p (hModel_of_U X hb u p hm), hImU_of_model X hb hK hL u p hm⟩` and prove the remaining obligations. Take `⟨_ψ, _c, π, _d, _, _, _, hπ, hker, _⟩` from `hm`. Conclude with `⟨π, hπ, hker⟩`.
-/
theorem locRedRest_of_models
    (h : ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, HModelU X hb u p) : LocRedRest := by
  intro D X hb hK u hM hL p
  have hm := h X hb hK u hM hL p
  refine ⟨?_, hLatGL_of_model X u p (hModel_of_U X hb u p hm), hImU_of_model X hb hK hL u p hm⟩
  obtain ⟨_ψ, _c, π, _d, _, _, _, hπ, hker, _⟩ := hm
  exact ⟨π, hπ, hker⟩

/- English proof (translation)
The claim follows from `idxCountStep_of_rest (locRedRest_of_models h)`.
-/
theorem idxCountStep_of_models
    (h : ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
      X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, HModelU X hb u p) : IdxCountStep :=
  idxCountStep_of_rest (locRedRest_of_models h)

end PIW.MassDataColumns
