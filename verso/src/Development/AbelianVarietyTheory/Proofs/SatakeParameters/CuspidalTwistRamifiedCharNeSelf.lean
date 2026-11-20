import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.TwistRamified

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (hρ : GlobalTheory.PRep.IsSmooth ρ) {H : Subgroup G} (hH : IsCompact (H : Set G))

include hρ hH in

/- English proof (translation)
Establish `h1 : v - GlobalTheory.LocGL.idem hρ hH v ∈ GlobalTheory.PRep.twKer ρ H 1` using `(GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).1 (by`. Rewrite using `[map_sub, GlobalTheory.LocGL.idem_of_mem hρ hH (GlobalTheory.LocGL.idem_mem hρ hH v), sub_self])`. Establish `h2 : T (v - GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.twKer ρ H 1`. Use `(Submodule.span_le (p := (GlobalTheory.PRep.twKer ρ H 1).comap T)).2 ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨n, w, rfl⟩`.

Use `Submodule.subset_span ⟨n, T w, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul]`. Conclude with `congrArg (· - _) (LinearMap.congr_fun (hT n) w)`. Establish `h3 : T (GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.fixed ρ H` using `GlobalTheory.LGrp.mem_fixed.2 fun k hk => by`. Rewrite using `[← Module.End.mul_apply, ← hT, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 (GlobalTheory.LocGL.idem_mem hρ hH v) k hk]`.

Rewrite using `[show T v = T (GlobalTheory.LocGL.idem hρ hH v) + T (v - GlobalTheory.LocGL.idem hρ hH v) by rw [← map_add, add_sub_cancel], map_add, GlobalTheory.LocGL.idem_of_mem hρ hH h3, (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).2 h2, add_zero]`.
-/
theorem idem_comm (T : Module.End ℂ V) (hT : ∀ g, T * ρ g = ρ g * T) (v : V) :
    T (GlobalTheory.LocGL.idem hρ hH v) = GlobalTheory.LocGL.idem hρ hH (T v) := by
  have h1 : v - GlobalTheory.LocGL.idem hρ hH v ∈ GlobalTheory.PRep.twKer ρ H 1 := (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).1 (by
    rw [map_sub, GlobalTheory.LocGL.idem_of_mem hρ hH (GlobalTheory.LocGL.idem_mem hρ hH v), sub_self])
  have h2 : T (v - GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.twKer ρ H 1 := by
    refine (Submodule.span_le (p := (GlobalTheory.PRep.twKer ρ H 1).comap T)).2 ?_ h1
    rintro _ ⟨n, w, rfl⟩
    refine Submodule.subset_span ⟨n, T w, ?_⟩
    rw [map_sub, map_smul]
    exact congrArg (· - _) (LinearMap.congr_fun (hT n) w)
  have h3 : T (GlobalTheory.LocGL.idem hρ hH v) ∈ GlobalTheory.PRep.fixed ρ H := GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
    rw [← Module.End.mul_apply, ← hT, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 (GlobalTheory.LocGL.idem_mem hρ hH v) k hk]
  rw [show T v = T (GlobalTheory.LocGL.idem hρ hH v) + T (v - GlobalTheory.LocGL.idem hρ hH v) by rw [← map_add, add_sub_cancel],
    map_add, GlobalTheory.LocGL.idem_of_mem hρ hH h3, (GlobalTheory.LocGL.idem_eq_zero_iff hρ hH).2 h2, add_zero]

end Gen

section Cusp

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Consider the cases of `o with`. Consider the case `fin k => exact (ho k rfl).elim`. Consider the case `cpt u`. Express the relevant statement in the definitionally equal form `(rt E a (infGL E a (Unitary.toUnits u)) * rt E a (finGL E a g)) y.1 = (rt E a (finGL E a g) * rt E a (infGL E a (Unitary.toUnits u))) y.1`.

Rewrite using `[← map_mul, ← map_mul, infGL_comm]`. Consider the case `lie X => exact LinearMap.congr_fun (lie_rt_fin X g) y.1`.
-/
theorem op_comm_fin (π : CuspSub E a) (o : Op E a) (ho : ∀ k, o ≠ .fin k) (g : GL (Fin a) (Af E)) (y : π.V) :
    π.op o (π.finPart g y) = π.finPart g (π.op o y) := by
  refine Subtype.ext ?_
  cases o with
  | fin k => exact (ho k rfl).elim
  | cpt u =>
    change (rt E a (infGL E a (Unitary.toUnits u)) * rt E a (finGL E a g)) y.1 =
      (rt E a (finGL E a g) * rt E a (infGL E a (Unitary.toUnits u))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X => exact LinearMap.congr_fun (lie_rt_fin X g) y.1

/- English proof (translation)
Establish `hi` using `Submodule.map_injective_of_injective π.V.injective_subtype`. Break down `π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by` into its components or cases. Introduce and unpack `o _ ⟨x, hx, rfl⟩`. Conclude with `⟨_, h o x hx, rfl⟩) with e | e`. Conclude with `Or.inl (hi (e.trans (Submodule.map_bot _).symm))`.

Conclude with `Or.inr (hi (e.trans (Submodule.map_subtype_top _).symm))`.
-/
theorem bot_or_top (π : CuspSub E a) (W : Submodule ℂ π.V) (h : ∀ o, ∀ x ∈ W, π.op o x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, h o x hx, rfl⟩) with e | e
  · exact Or.inl (hi (e.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (e.trans (Submodule.map_subtype_top _).symm))

end Cusp

end GlobalTheory.TwistRamified

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep Matrix

namespace GlobalTheory.TwistRamified

section Local

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `letI := GlobalTheory.LocalData.complRel v`. Use `haveI := GlobalTheory.LocalData.isLocalField v`. Establish `hK : GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL v a` using `GlobalTheory.SmGL.SphCompletion.KO_completion v a`. Take `⟨x, hx, y, hy, t, rfl⟩` from `GlobalTheory.LocalCartan.exists_diagT (n := Fin a) g`. Rewrite `hx`, `hy` using `[hK]`.

Establish `hu1 : Valued.v (u : v.adicCompletion E) ≤ 1` using `le_of_eq hu`. Establish `hu2 : Valued.v ((u⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (u : v.adicCompletion E) = 1 from hu, inv_one]`. Set `u' : (Formalism.UG.Ov E v)ˣ` to `⟨⟨u, hu1⟩, ⟨(u⁻¹ : (v.adicCompletion E)ˣ), hu2⟩, Subtype.ext (Units.mul_inv u), Subtype.ext (Units.inv_mul u)⟩`. Set `i₀ : Fin a` to `⟨0, ha⟩`.

Set `d` to `GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) (Pi.mulSingle i₀ u)`. Establish `hd : d ∈ GlobalTheory.LFun.KGL v a`. Use `⟨GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u'), Units.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Formalism.UG.Ov E v).subtype.mapMatrix (GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u')).val : Matrix (Fin a) (Fin a) (v.adicCompletion E)) = (d : Matrix (Fin a) (Fin a) (v.adicCompletion E))`. Rewrite using `[GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality.

Simplify using `[u']`. Simplify using `[hi]`. Simplify using `[hij]`. Establish `hdt : (GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t)⁻¹ * d * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t = d`. Rewrite using `[← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]`.

Use `⟨x * d * x⁻¹, mul_mem (mul_mem hx hd) (inv_mem hx), ?_, ?_⟩` and prove the remaining obligations. Establish `e : (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y)⁻¹ * (x * d * x⁻¹) * (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y) = y⁻¹ * d * y` using `by conv_rhs => rw [← hdt] group`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem (inv_mem hy) hd) hy`. Establish `hdet : GeneralLinearGroup.det d = u`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal]`. Rewrite using `[Finset.prod_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[map_mul, map_mul, map_inv, hdet, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]`.
-/
theorem exists_conj_mem {a : ℕ} (ha : 1 ≤ a) (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (v.adicCompletion E))
    (u : (v.adicCompletion E)ˣ) (hu : IsUnitAt v u) :
    ∃ h ∈ GlobalTheory.LFun.KGL v a, g⁻¹ * h * g ∈ GlobalTheory.LFun.KGL v a ∧ GeneralLinearGroup.det h = u := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  have hK : GlobalTheory.SplitWeil.KO (v.adicCompletion E) (Fin a) = GlobalTheory.LFun.KGL v a :=
    GlobalTheory.SmGL.SphCompletion.KO_completion v a
  obtain ⟨x, hx, y, hy, t, rfl⟩ := GlobalTheory.LocalCartan.exists_diagT (n := Fin a) g
  rw [hK] at hx hy
  have hu1 : Valued.v (u : v.adicCompletion E) ≤ 1 := le_of_eq hu
  have hu2 : Valued.v ((u⁻¹ : (v.adicCompletion E)ˣ) : v.adicCompletion E) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (u : v.adicCompletion E) = 1 from hu, inv_one]
  let u' : (Formalism.UG.Ov E v)ˣ := ⟨⟨u, hu1⟩, ⟨(u⁻¹ : (v.adicCompletion E)ˣ), hu2⟩,
    Subtype.ext (Units.mul_inv u), Subtype.ext (Units.inv_mul u)⟩
  let i₀ : Fin a := ⟨0, ha⟩
  let d := GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) (Pi.mulSingle i₀ u)
  have hd : d ∈ GlobalTheory.LFun.KGL v a := by
    refine ⟨GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u'), Units.ext ?_⟩
    change ((Formalism.UG.Ov E v).subtype.mapMatrix (GlobalTheory.SmGL.diagT (Formalism.UG.Ov E v) (Fin a) (Pi.mulSingle i₀ u')).val :
      Matrix (Fin a) (Fin a) (v.adicCompletion E)) = (d : Matrix (Fin a) (Fin a) (v.adicCompletion E))
    rw [GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = i₀
      · subst hi; simp [u']
      · simp [hi]
    · simp [hij]
  have hdt : (GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t)⁻¹ * d * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t = d := by
    rw [← map_inv, ← map_mul, ← map_mul, inv_mul_cancel_comm]
  refine ⟨x * d * x⁻¹, mul_mem (mul_mem hx hd) (inv_mem hx), ?_, ?_⟩
  · have e : (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y)⁻¹ * (x * d * x⁻¹) *
        (x * GlobalTheory.SmGL.diagT (v.adicCompletion E) (Fin a) t * y) = y⁻¹ * d * y := by
      conv_rhs => rw [← hdt]
      group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hy) hd) hy
  · have hdet : GeneralLinearGroup.det d = u := by
      refine Units.ext ?_
      rw [GeneralLinearGroup.val_det_apply, GlobalTheory.SmGL.val_diagT, Matrix.det_diagonal]
      rw [Finset.prod_eq_single i₀ (fun j _ hj => by simp [hj]) (by simp)]
      simp
    rw [map_mul, map_mul, map_inv, hdet, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]

/- English proof (translation)
Establish `key : ∀ w, GeneralLinearGroup.map (pLoc E w) (g⁻¹ * locGL E a v h * g) = GeneralLinearGroup.map (pLoc E w) (locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h * GeneralLinearGroup.map (pLoc E v) g))`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[pLoc_locGL, map_mul, map_mul, map_inv, pLoc_locGL]`.

Rewrite using `[pLoc_locGL_of_ne hw, map_mul, map_mul, pLoc_locGL_of_ne hw, mul_one, map_inv, inv_mul_cancel]`. Use `Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun w => ?_)` and prove the remaining obligations. Conclude with `congrArg (fun M : GL (Fin a) (w.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) (key w)`.
-/
theorem conj_locGL {a : ℕ} (v : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (Af E))
    (h : GL (Fin a) (v.adicCompletion E)) :
    g⁻¹ * locGL E a v h * g = locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
      GeneralLinearGroup.map (pLoc E v) g) := by
  have key : ∀ w, GeneralLinearGroup.map (pLoc E w) (g⁻¹ * locGL E a v h * g) =
      GeneralLinearGroup.map (pLoc E w) (locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
        GeneralLinearGroup.map (pLoc E v) g)) := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [pLoc_locGL, map_mul, map_mul, map_inv, pLoc_locGL]
    · rw [pLoc_locGL_of_ne hw, map_mul, map_mul, pLoc_locGL_of_ne hw, mul_one, map_inv, inv_mul_cancel]
  refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun w => ?_)
  exact congrArg (fun M : GL (Fin a) (w.adicCompletion E) => (M : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j)
    (key w)

end Local

end GlobalTheory.TwistRamified

namespace GlobalTheory.TwistRamified

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Use `set χ := CuspSub.locDet a η v with hχdef`. Establish `hχs : GlobalTheory.SmGL.IsSmoothChar χ⁻¹` using `GlobalTheory.SmGL.IsSmoothChar.inv (CuspSub.isOpen_ker_locDet (a := a) η v)`. Establish `hρ` using `p.isSmooth_locRep v`. Establish `hρ'` using `GlobalTheory.SmGL.isSmooth_twist hρ hχs`. Establish `hK` using `(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v a).2`.

Use `set P := GlobalTheory.LocGL.idem hρ' hK with hPdef`. Establish `hρ'app : ∀ g z, GlobalTheory.SmGL.twist (p.locRep v) χ⁻¹ g z = ((χ g : ℂˣ) : ℂ)⁻¹ • p.locRep v g z` using `fun g z => by`. Simplify using the standard rewrite rules. Establish `hPeq : ∀ k ∈ GlobalTheory.LFun.KGL v a, ∀ z, P (p.locRep v k z) = ((χ k : ℂˣ) : ℂ) • P z` using `fun k hk z => by`. Establish `h1` using `GlobalTheory.LocGL.idem_apply_mem hρ' hK hk z`.

Rewrite `h1` using `[hρ'app, map_smul]`. Rewrite using `[← h1, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]`. Establish `hPfix : P y = y`. Use `GlobalTheory.LocGL.idem_of_mem hρ' hK (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_)` and prove the remaining obligations. Rewrite using `[hρ'app, hy k hk, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]`.

Establish `hPzero : ∀ z, ∀ h ∈ GlobalTheory.LFun.KGL v a, χ h ≠ 1 → p.locRep v h z = z → P z = 0` using `fun z h hh hc hz => by`. Establish `h1` using `hPeq h hh z`. Rewrite `h1` using `[hz]`. Establish `h2 : (((χ h : ℂˣ) : ℂ) - 1) • P z = 0` using `by rw [sub_smul, ← h1, one_smul, sub_self]`. Use `(smul_eq_zero.1 h2).resolve_left fun h0 => hc (Units.ext ?_)` and prove the remaining obligations.

Rewrite using `[Units.val_one]`. Conclude with `sub_eq_zero.1 h0`. Establish `hPcomm : ∀ o : Op E a, (∀ k, o ≠ .fin k) → ∀ z, P (p.op o z) = p.op o (P z)` using `fun o ho z => by`. Establish `h1` using `idem_comm hρ' hK (p.op o) (fun g => by`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations.

Simplify using `only [Module.End.mul_apply, hρ'app, map_smul]`. Use `congr 1`. Conclude with `op_comm_fin p o ho (locGL E a v g) w) z`. Conclude with `h1.symm`. Establish `hPx : ∀ g : GL (Fin a) (Af E), P (p.finPart g x) = 0` using `fun g => by`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu, hu1⟩ : ∃ u, IsUnitAt v u ∧ η.loc v u ≠ 1 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hη hc`. Take `⟨h, hh, hgh, hdet⟩` from `exists_conj_mem ha v (GeneralLinearGroup.map (pLoc E v) g) u hu`.

Use `hPzero _ h hh (by rw [hχdef, CuspSub.locDet, MonoidHom.comp_apply, hdet]; exact hu1) ?_` and prove the remaining obligations. Establish `e : locGL E a v h * g = g * locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h * GeneralLinearGroup.map (pLoc E v) g)`. Rewrite using `[← conj_locGL]`. Use `group`. Express the relevant statement in the definitionally equal form `p.finPart (locGL E a v h) (p.finPart g x) = _`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]`. Use `congr 1`. Conclude with `GlobalTheory.LGrp.mem_fixed.1 hx _ hgh`. Set `W : Submodule ℂ p.V` to `{ carrier := {φ | ∀ g, P (p.finPart g φ) = 0} add_mem' := fun {φ ψ} hφ hψ g => by rw [map_add, map_add, hφ g, hψ g, add_zero] zero_mem' := fun g => by rw [map_zero, map_zero] smul_mem' := fun c φ hφ g => by`. Express the relevant statement in the definitionally equal form `P (p.finPart g (c • φ)) = 0`.

Rewrite using `[map_smul, map_smul, hφ g, smul_zero] }`. Establish `hW : ∀ o, ∀ φ ∈ W, p.op o φ ∈ W`. Introduce `o φ hφ g`. Distinguish the cases in `ho : ∀ k, o ≠ .fin k`. Rewrite using `[← op_comm_fin p o ho, hPcomm o ho]`.

Express the relevant statement in the definitionally equal form `p.op o (P (p.finPart g φ)) = 0`. Rewrite using `[hφ g, map_zero]`. Use `push_neg at ho`. Take `⟨k, rfl⟩` from `ho`. Establish `e : p.finPart g (p.op (.fin k) φ) = p.finPart (g * k) φ`.

Rewrite using `[map_mul, Module.End.mul_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `hφ (g * k)`. Break down `bot_or_top p W hW with h | h` into its components or cases.

Conclude with `absurd ((Submodule.mem_bot ℂ).1 (h ▸ (show x ∈ W from hPx))) hx0`. Establish `h1 : y ∈ W` using `h ▸ Submodule.mem_top`. Establish `h2` using `h1 1`. Rewrite `h2` using `[map_one, Module.End.one_apply, hPfix]`. Then use the resulting hypothesis.
-/
theorem no_eigvec (p : CuspSub E a) (ha : 1 ≤ a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (hη : ¬ η.UnrAt v)
    {x : p.V} (hx : x ∈ GlobalTheory.PRep.fixed (p.locRep v) (GlobalTheory.LFun.KGL v a)) (hx0 : x ≠ 0) (y : p.V)
    (hy : ∀ k ∈ GlobalTheory.LFun.KGL v a, p.locRep v k y = ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • y) : y = 0 := by
  set χ := CuspSub.locDet a η v with hχdef
  have hχs : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := GlobalTheory.SmGL.IsSmoothChar.inv (CuspSub.isOpen_ker_locDet (a := a) η v)
  have hρ := p.isSmooth_locRep v
  have hρ' := GlobalTheory.SmGL.isSmooth_twist hρ hχs
  have hK := (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL v a).2
  set P := GlobalTheory.LocGL.idem hρ' hK with hPdef
  have hρ'app : ∀ g z, GlobalTheory.SmGL.twist (p.locRep v) χ⁻¹ g z = ((χ g : ℂˣ) : ℂ)⁻¹ • p.locRep v g z := fun g z => by
    simp

  have hPeq : ∀ k ∈ GlobalTheory.LFun.KGL v a, ∀ z, P (p.locRep v k z) = ((χ k : ℂˣ) : ℂ) • P z := fun k hk z => by
    have h1 := GlobalTheory.LocGL.idem_apply_mem hρ' hK hk z
    rw [hρ'app, map_smul] at h1
    rw [← h1, smul_smul, mul_inv_cancel₀ (Units.ne_zero _), one_smul]
  have hPfix : P y = y := by
    refine GlobalTheory.LocGL.idem_of_mem hρ' hK (GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_)
    rw [hρ'app, hy k hk, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
  have hPzero : ∀ z, ∀ h ∈ GlobalTheory.LFun.KGL v a, χ h ≠ 1 → p.locRep v h z = z → P z = 0 := fun z h hh hc hz => by
    have h1 := hPeq h hh z
    rw [hz] at h1
    have h2 : (((χ h : ℂˣ) : ℂ) - 1) • P z = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    refine (smul_eq_zero.1 h2).resolve_left fun h0 => hc (Units.ext ?_)
    rw [Units.val_one]; exact sub_eq_zero.1 h0

  have hPcomm : ∀ o : Op E a, (∀ k, o ≠ .fin k) → ∀ z, P (p.op o z) = p.op o (P z) := fun o ho z => by
    have h1 := idem_comm hρ' hK (p.op o) (fun g => by
      refine LinearMap.ext fun w => ?_
      simp only [Module.End.mul_apply, hρ'app, map_smul]
      congr 1
      exact op_comm_fin p o ho (locGL E a v g) w) z
    exact h1.symm

  have hPx : ∀ g : GL (Fin a) (Af E), P (p.finPart g x) = 0 := fun g => by
    obtain ⟨u, hu, hu1⟩ : ∃ u, IsUnitAt v u ∧ η.loc v u ≠ 1 := by
      by_contra hc
      push_neg at hc
      exact hη hc
    obtain ⟨h, hh, hgh, hdet⟩ := exists_conj_mem ha v (GeneralLinearGroup.map (pLoc E v) g) u hu
    refine hPzero _ h hh (by rw [hχdef, CuspSub.locDet, MonoidHom.comp_apply, hdet]; exact hu1) ?_
    have e : locGL E a v h * g = g * locGL E a v ((GeneralLinearGroup.map (pLoc E v) g)⁻¹ * h *
        GeneralLinearGroup.map (pLoc E v) g) := by
      rw [← conj_locGL]; group
    change p.finPart (locGL E a v h) (p.finPart g x) = _
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    congr 1
    exact GlobalTheory.LGrp.mem_fixed.1 hx _ hgh

  let W : Submodule ℂ p.V :=
    { carrier := {φ | ∀ g, P (p.finPart g φ) = 0}
      add_mem' := fun {φ ψ} hφ hψ g => by rw [map_add, map_add, hφ g, hψ g, add_zero]
      zero_mem' := fun g => by rw [map_zero, map_zero]
      smul_mem' := fun c φ hφ g => by
        change P (p.finPart g (c • φ)) = 0
        rw [map_smul, map_smul, hφ g, smul_zero] }
  have hW : ∀ o, ∀ φ ∈ W, p.op o φ ∈ W := by
    intro o φ hφ g
    by_cases ho : ∀ k, o ≠ .fin k
    · rw [← op_comm_fin p o ho, hPcomm o ho]
      change p.op o (P (p.finPart g φ)) = 0
      rw [hφ g, map_zero]
    · push_neg at ho
      obtain ⟨k, rfl⟩ := ho
      have e : p.finPart g (p.op (.fin k) φ) = p.finPart (g * k) φ := by
        rw [map_mul, Module.End.mul_apply]; rfl
      rw [e]
      exact hφ (g * k)
  rcases bot_or_top p W hW with h | h
  · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ (show x ∈ W from hPx))) hx0
  · have h1 : y ∈ W := h ▸ Submodule.mem_top
    have h2 := h1 1
    rwa [map_one, Module.End.one_apply, hPfix] at h2

end GlobalTheory.TwistRamified

open GlobalTheory.CuspRep in

/- English proof (translation)
Introduce `E _ _ _ a ha π η v B hB hη`. Proceed by induction on `π using Quotient.inductionOn with | _ p => ?_`. Introduce `e`. Take `⟨T, hT⟩ : CuspSub.Iso (p.twist η) p` from `Quotient.exact e`. Establish `hB' : GlobalTheory.LFun.HasSatGL v (p.locRep v) B` using `hB`.

Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hB'.1`. Establish `hy : ∀ k ∈ GlobalTheory.LFun.KGL v a, p.locRep v k (T (p.toTwist η x)) = ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • T (p.toTwist η x)` using `fun k hk => by`. Rewrite using `[CuspSub.locRep_eq, ← hT, CuspSub.op_toTwist, ← CuspSub.locRep_eq, GlobalTheory.LGrp.mem_fixed.1 hx k hk]`. Simplify using `only [opAdd, zero_smul, add_zero, map_smul]`. Use `congr 2`.

Conclude with `CuspSub.chiDet_locGL η v k`. Establish `h0` using `GlobalTheory.TwistRamified.no_eigvec p ha η v hη hx hx0 _ hy`. Conclude with `hx0 ((p.toTwist η).injective (T.injective (h0.trans (map_zero T).symm) |>.trans (map_zero _).symm))`.
-/
theorem GlobalTheory.TwistRamified.twist_ne : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π : CG E a) (η : HChar E) (v : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), π.HasSat v B → ¬ η.UnrAt v →
    π.twist η ≠ π := by
  intro E _ _ _ a ha π η v B hB hη
  induction π using Quotient.inductionOn with | _ p => ?_
  intro e
  obtain ⟨T, hT⟩ : CuspSub.Iso (p.twist η) p := Quotient.exact e
  have hB' : GlobalTheory.LFun.HasSatGL v (p.locRep v) B := hB
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hB'.1
  have hy : ∀ k ∈ GlobalTheory.LFun.KGL v a, p.locRep v k (T (p.toTwist η x)) =
      ((CuspSub.locDet a η v k : ℂˣ) : ℂ) • T (p.toTwist η x) := fun k hk => by
    rw [CuspSub.locRep_eq, ← hT, CuspSub.op_toTwist, ← CuspSub.locRep_eq, GlobalTheory.LGrp.mem_fixed.1 hx k hk]
    simp only [opAdd, zero_smul, add_zero, map_smul]
    congr 2
    exact CuspSub.chiDet_locGL η v k
  have h0 := GlobalTheory.TwistRamified.no_eigvec p ha η v hη hx hx0 _ hy
  exact hx0 ((p.toTwist η).injective (T.injective (h0.trans (map_zero T).symm) |>.trans (map_zero _).symm))
