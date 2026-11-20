import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.ContinuousAdmissibleReps.AdmissibleDiscreteSpaces
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import PositivityTheory.AutomorphicForms.PublishedInputs.BorelInjectivity.EquivariantProjections.ExistsEquivariantProjOfLeSumIrreducible

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.F5.Bo.FiniteIsomorphism

open PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDiscPf

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

/- English proof (translation)
Take `⟨T, hT⟩` from `h`. Use `⟨T.symm, fun o φ ψ hψ => ?_⟩` and prove the remaining obligations. Use `set a := T.symm φ with ha`. Set `b : V` to `⟨act o a.1, hV o a.1 a.2⟩`. Establish `hb : T b = ψ`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hT o a b rfl, ha, LinearEquiv.apply_symm_apply]`. Conclude with `hψ.symm`. Rewrite using `[← hb, LinearEquiv.symm_apply_apply]`.
-/
theorem isoV_symm {V V' : Submodule ℂ (Sm E N)} (hV : IsStable V) (h : SpectralAccumulation.IsoV V V') : SpectralAccumulation.IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ hψ => ?_⟩
  set a := T.symm φ with ha
  let b : V := ⟨act o a.1, hV o a.1 a.2⟩
  have hb : T b = ψ := by
    apply Subtype.ext
    rw [hT o a b rfl, ha, LinearEquiv.apply_symm_apply]
    exact hψ.symm
  rw [← hb, LinearEquiv.symm_apply_apply]

/- English proof (translation)
Establish `hker : V ⊓ LinearMap.ker f = ⊥`. Break down `hV.irred (V ⊓ LinearMap.ker f) inf_le_left (fun o x hx => Submodule.mem_inf.2 ⟨hV.stable o x (Submodule.mem_inf.1 hx).1, LinearMap.mem_ker.2 (by rw [hf o x (Submodule.mem_inf.1 hx).1, LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2, map_zero])⟩) with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Take `⟨x, hx, hx0⟩` from `hne`.

Establish `: x ∈ V ⊓ LinearMap.ker f` using `by rw [h]; exact hx`. Conclude with `hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)`. Establish `himg : V.map f = V'`. Break down `hV'.irred (V.map f) (Submodule.map_le_iff_le_comap.2 fun x hx => hfV x hx) (fun o y hy => by` into its components or cases. Take `⟨x, hx, rfl⟩` from `hy`.

Conclude with `⟨act o x, hV.stable o x hx, hf o x hx⟩) with h | h`. It suffices to derive a contradiction. Take `⟨x, hx, hx0⟩` from `hne`. Conclude with `hx0 ((Submodule.mem_bot ℂ).1 (h ▸ Submodule.mem_map_of_mem hx))`. Conclude with `h`.

Set `g : V →ₗ[ℂ] V'` to `(f.comp V.subtype).codRestrict V' (fun x => hfV x.1 x.2)`. Establish `hinj : Function.Injective g`. Introduce `x y hxy`. Establish `h1 : f x.1 = f y.1` using `congrArg Subtype.val hxy`. Establish `h2 : x.1 - y.1 ∈ V ⊓ LinearMap.ker f` using `Submodule.mem_inf.2 ⟨V.sub_mem x.2 y.2, LinearMap.mem_ker.2 (by rw [map_sub, h1, sub_self])⟩`.

Rewrite `h2` using `[hker, Submodule.mem_bot, sub_eq_zero]`. Conclude with `Subtype.ext h2`. Establish `hsurj : Function.Surjective g`. Introduce `y`. Establish `: y.1 ∈ V.map f` using `himg ▸ y.2`.

Take `⟨x, hx, hxy⟩` from `this`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxy⟩`. Use `⟨LinearEquiv.ofBijective g ⟨hinj, hsurj⟩, fun o φ ψ hψ => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f ψ.1 = act o (f φ.1)`. Rewrite using `[hψ, hf o φ.1 φ.2]`.
-/
theorem isoV_of_map {V V' : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (hV' : IsDiscrete V')
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ x ∈ V, f (act o x) = act o (f x)) (hfV : ∀ x ∈ V, f x ∈ V')
    (hne : ∃ x ∈ V, f x ≠ 0) : SpectralAccumulation.IsoV V V' := by
  have hker : V ⊓ LinearMap.ker f = ⊥ := by
    rcases hV.irred (V ⊓ LinearMap.ker f) inf_le_left (fun o x hx => Submodule.mem_inf.2 ⟨hV.stable o x (Submodule.mem_inf.1 hx).1,
        LinearMap.mem_ker.2 (by rw [hf o x (Submodule.mem_inf.1 hx).1,
          LinearMap.mem_ker.1 (Submodule.mem_inf.1 hx).2, map_zero])⟩) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, hx0⟩ := hne
      have : x ∈ V ⊓ LinearMap.ker f := by rw [h]; exact hx
      exact hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
  have himg : V.map f = V' := by
    rcases hV'.irred (V.map f) (Submodule.map_le_iff_le_comap.2 fun x hx => hfV x hx) (fun o y hy => by
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨act o x, hV.stable o x hx, hf o x hx⟩) with h | h
    · exfalso
      obtain ⟨x, hx, hx0⟩ := hne
      exact hx0 ((Submodule.mem_bot ℂ).1 (h ▸ Submodule.mem_map_of_mem hx))
    · exact h
  let g : V →ₗ[ℂ] V' := (f.comp V.subtype).codRestrict V' (fun x => hfV x.1 x.2)
  have hinj : Function.Injective g := by
    intro x y hxy
    have h1 : f x.1 = f y.1 := congrArg Subtype.val hxy
    have h2 : x.1 - y.1 ∈ V ⊓ LinearMap.ker f :=
      Submodule.mem_inf.2 ⟨V.sub_mem x.2 y.2, LinearMap.mem_ker.2 (by rw [map_sub, h1, sub_self])⟩
    rw [hker, Submodule.mem_bot, sub_eq_zero] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective g := by
    intro y
    have : y.1 ∈ V.map f := himg ▸ y.2
    obtain ⟨x, hx, hxy⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  refine ⟨LinearEquiv.ofBijective g ⟨hinj, hsurj⟩, fun o φ ψ hψ => ?_⟩
  change f ψ.1 = act o (f φ.1)
  rw [hψ, hf o φ.1 φ.2]

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hs i hi`. Take `⟨p, -, -, hpid, hp0⟩` from `GlobalTheory.BorelCoh.exists_equivariant_proj_of_irreducible_family (Sm E N) (Op E N) (Fin k) act V (fun i => (hV i).stable) (fun i => (hV i).ne_bot) (fun i W hW hst => (hV i).irred W hW hst) (fun i j hij f hf hfV x hx => by`. Assume the negation of the conclusion as `hx0`. Conclude with `hn i j hij (isoV_of_map (hV i) (hV j) f hf hfV ⟨x, hx, hx0⟩)) i`.

Establish `h` using `congrArg p hs`. Rewrite `h` using `[map_sum, map_zero, Finset.sum_eq_single i (fun j _ hji => by rw [map_smul, hp0 j hji _ (hφV j), smul_zero]) (fun h' => absurd hi h'), map_smul, hpid _ (hφV i)]`. Conclude with `(smul_eq_zero.1 h).resolve_right (hφ0 i)`.
-/
theorem linIndep {k : ℕ} (V : Fin k → Submodule ℂ (Sm E N)) (hV : ∀ i, IsDiscrete (V i))
    (hn : ∀ i j, i ≠ j → ¬ SpectralAccumulation.IsoV (V i) (V j)) (φ : Fin k → Sm E N) (hφV : ∀ i, φ i ∈ V i)
    (hφ0 : ∀ i, φ i ≠ 0) : LinearIndependent ℂ φ := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  obtain ⟨p, -, -, hpid, hp0⟩ := GlobalTheory.BorelCoh.exists_equivariant_proj_of_irreducible_family (Sm E N) (Op E N)
    (Fin k) act V (fun i => (hV i).stable) (fun i => (hV i).ne_bot) (fun i W hW hst => (hV i).irred W hW hst)
    (fun i j hij f hf hfV x hx => by
      by_contra hx0
      exact hn i j hij (isoV_of_map (hV i) (hV j) f hf hfV ⟨x, hx, hx0⟩)) i
  have h := congrArg p hs
  rw [map_sum, map_zero, Finset.sum_eq_single i (fun j _ hji => by rw [map_smul, hp0 j hji _ (hφV j), smul_zero])
    (fun h' => absurd hi h'), map_smul, hpid _ (hφV i)] at h
  exact (smul_eq_zero.1 h).resolve_right (hφ0 i)

/- English proof (translation)
Use `⟨hV.aut φ hφ, fun k hk => Subtype.ext (funext fun g => hT.1 k hk g), fun g => ?_, fun τ u => (hinf τ).2 u φ hφ⟩` and prove the remaining obligations. Establish `hf : (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ lI (W ⊓ contK E N)`. Use `mem_lI.2 fun k₀ => ⟨?_, ?_⟩` and prove the remaining obligations. Use `show (fun k => φ.1 (g * infGL E N (Unitary.toUnits (k₀ * k)))) ∈ W`. Use `hT.2 (g * infGL E N (Unitary.toUnits k₀))` as an intermediate fact.

Simplify `this` using `only [map_mul, mul_assoc]`. Use `show Continuous fun k => φ.1 (g * infGL E N (Unitary.toUnits (k₀ * k)))`. Use `cont_K φ (g * infGL E N (Unitary.toUnits k₀))` as an intermediate fact. Simplify `this` using `only [map_mul, mul_assoc]`. Establish `hfU` using `le_rS _ hf`.

Use `Submodule.subset_span ⟨(LinearMap.proj 1 : (Kinf E N → ℂ) →ₗ[ℂ] ℂ).comp (rS (lI (W ⊓ contK E N))).subtype, ⟨_, hfU⟩, funext fun k => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(cptRep E N k φ).1 g = (cptRep E N (1 * k) φ).1 g`. Rewrite using `[one_mul]`.
-/
theorem mem_forms_of {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {m : (E →+* ℂ) → Multiset ℂ} (hU : ∀ u ∈ rS (lI (W ⊓ contK E N)), ∀ k,
      (fun x => u (x * k)) ∈ rS (lI (W ⊓ contK E N)))
    {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) (hinf : ∀ τ, HasInfCharGL V τ (m τ)) {φ : Sm E N}
    (hφ : φ ∈ V) (hT : SpectralAccumulation.TypeB K W φ) :
    φ ∈ GlobalTheory.Published.AutFinGL.forms K (rR (rS (lI (W ⊓ contK E N))) hU)
      (fun τ u => ((m τ).map (u + ·)).prod) := by
  refine ⟨hV.aut φ hφ, fun k hk => Subtype.ext (funext fun g => hT.1 k hk g), fun g => ?_,
    fun τ u => (hinf τ).2 u φ hφ⟩
  have hf : (fun k : Kinf E N => (cptRep E N k φ).1 g) ∈ lI (W ⊓ contK E N) := by
    refine mem_lI.2 fun k₀ => ⟨?_, ?_⟩
    · show (fun k => φ.1 (g * infGL E N (Unitary.toUnits (k₀ * k)))) ∈ W
      have := hT.2 (g * infGL E N (Unitary.toUnits k₀))
      simpa only [map_mul, mul_assoc] using this
    · show Continuous fun k => φ.1 (g * infGL E N (Unitary.toUnits (k₀ * k)))
      have := cont_K φ (g * infGL E N (Unitary.toUnits k₀))
      simpa only [map_mul, mul_assoc] using this
  have hfU := le_rS _ hf
  refine Submodule.subset_span ⟨(LinearMap.proj 1 : (Kinf E N → ℂ) →ₗ[ℂ] ℂ).comp
    (rS (lI (W ⊓ contK E N))).subtype, ⟨_, hfU⟩, funext fun k => ?_⟩
  change (cptRep E N k φ).1 g = (cptRep E N (1 * k) φ).1 g
  rw [one_mul]

end PositivityTheory.Rg.BcB.F.F5.Bo.FiniteIsomorphism

namespace PositivityTheory.Rg.BcB.F.F5.Bo

open PositivityTheory.Rg.BcB.SpectralAccumulation.AdmDiscPf FiniteIsomorphism

/- English proof (translation)
Introduce `E _ _ _ N K W m hK hW`. Establish `: FiniteDimensional ℂ (W ⊓ contK E N : Submodule ℂ (Kinf E N → ℂ))` using `Submodule.finiteDimensional_of_le inf_le_left`. Establish `: FiniteDimensional ℂ (rS (lI (W ⊓ contK E N)))` using `fd_rS_lI _`. Establish `hU : ∀ u ∈ rS (lI (W ⊓ contK E N)), ∀ k, (fun x => u (x * k)) ∈ rS (lI (W ⊓ contK E N))` using `fun u hu k => rS_right hu k`. Set `F` to `Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (rR (rS (lI (W ⊓ contK E N))) hU) (fun τ u => ((m τ).map (u + ·)).prod))`.

Establish `: FiniteDimensional ℂ F` using `PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N K hK _ (rR (rS (lI (W ⊓ contK E N))) hU) (isContRep_rR _ hU (cont_rS W)) _`. Set `P : Submodule ℂ (Sm E N) → Prop` to `fun V => IsDiscrete V ∧ SpectralAccumulation.HasType K W V ∧ ∀ τ, HasInfCharGL V τ (m τ)`. Set `G : ℕ → Prop` to `fun l => ∃ V : Fin l → Submodule ℂ (Sm E N), (∀ i, P (V i)) ∧ ∀ i j, i ≠ j → ¬ SpectralAccumulation.IsoV (V i) (V j)`. Establish `hbound : ∀ l, G l → l ≤ Module.finrank ℂ F`. Introduce and unpack `l ⟨V, hVP, hVn⟩`.

Use `choose φ hφV hφ0 hφT using fun i => (hVP i).2.1`. Establish `hmem : ∀ i, φ i ∈ F` using `fun i => Submodule.subset_span (mem_forms_of hU (hVP i).1 (hVP i).2.2 (hφV i) (hφT i))`. Establish `hli` using `linIndep V (fun i => (hVP i).1) hVn φ hφV hφ0`. Establish `hli' : LinearIndependent ℂ (fun i => (⟨φ i, hmem i⟩ : F))` using `LinearIndependent.of_comp F.subtype hli`. Simplify using `using hli'.fintype_card_le_finrank`.

Establish `h0 : G 0` using `⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩`. Establish `hl : G (Nat.findGreatest G (Module.finrank ℂ F))` using `Nat.findGreatest_spec (Nat.zero_le _) h0`. Take `⟨V, hVP, hVn⟩` from `hl`. Use `⟨Finset.univ.image V, fun V' hV' => ?_, fun V' hd ht hi => ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hV'`.

Conclude with `(hVP i).1`. Assume the negation of the conclusion as `hno push Not at hno`. Establish `hno' : ∀ i, ¬ SpectralAccumulation.IsoV V' (V i)` using `fun i => hno (V i) (Finset.mem_image_of_mem V (Finset.mem_univ i))`. Establish `hG : G (Nat.findGreatest G (Module.finrank ℂ F) + 1)`. Use `⟨Fin.cons V' V, fun i => ?_, fun i j hij => ?_⟩` and prove the remaining obligations.

Break down `Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩` into its components or cases. Conclude with `⟨hd, ht, hi⟩`. Simplify `hVP i'` using `only [Fin.cons_succ]`. Apply the tactic sequence `rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>`. Break down `Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩` into its components or cases.

Conclude with `absurd rfl hij`. Simplify `hno' j'` using `only [Fin.cons_zero, Fin.cons_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Conclude with `fun h => hno' i' (isoV_symm (hVP i').1.stable h)`. Simplify using `only [Fin.cons_succ]`.

Conclude with `hVn i' j' (fun h => hij (by rw [h]))`. Use `Nat.le_findGreatest (hbound _ hG) hG` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem FinIso_holds : FinIso := by
  intro E _ _ _ N K W m hK hW
  classical
  have : FiniteDimensional ℂ (W ⊓ contK E N : Submodule ℂ (Kinf E N → ℂ)) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have : FiniteDimensional ℂ (rS (lI (W ⊓ contK E N))) := fd_rS_lI _
  have hU : ∀ u ∈ rS (lI (W ⊓ contK E N)), ∀ k, (fun x => u (x * k)) ∈ rS (lI (W ⊓ contK E N)) :=
    fun u hu k => rS_right hu k
  let F := Submodule.span ℂ (GlobalTheory.Published.AutFinGL.forms K (rR (rS (lI (W ⊓ contK E N))) hU)
    (fun τ u => ((m τ).map (u + ·)).prod))
  have : FiniteDimensional ℂ F := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E N K hK _
    (rR (rS (lI (W ⊓ contK E N))) hU) (isContRep_rR _ hU (cont_rS W)) _
  let P : Submodule ℂ (Sm E N) → Prop := fun V =>
    IsDiscrete V ∧ SpectralAccumulation.HasType K W V ∧ ∀ τ, HasInfCharGL V τ (m τ)
  let G : ℕ → Prop := fun l => ∃ V : Fin l → Submodule ℂ (Sm E N), (∀ i, P (V i)) ∧
    ∀ i j, i ≠ j → ¬ SpectralAccumulation.IsoV (V i) (V j)
  have hbound : ∀ l, G l → l ≤ Module.finrank ℂ F := by
    rintro l ⟨V, hVP, hVn⟩
    choose φ hφV hφ0 hφT using fun i => (hVP i).2.1
    have hmem : ∀ i, φ i ∈ F := fun i =>
      Submodule.subset_span (mem_forms_of hU (hVP i).1 (hVP i).2.2 (hφV i) (hφT i))
    have hli := linIndep V (fun i => (hVP i).1) hVn φ hφV hφ0
    have hli' : LinearIndependent ℂ (fun i => (⟨φ i, hmem i⟩ : F)) :=
      LinearIndependent.of_comp F.subtype hli
    simpa using hli'.fintype_card_le_finrank
  have h0 : G 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hl : G (Nat.findGreatest G (Module.finrank ℂ F)) := Nat.findGreatest_spec (Nat.zero_le _) h0
  obtain ⟨V, hVP, hVn⟩ := hl
  refine ⟨Finset.univ.image V, fun V' hV' => ?_, fun V' hd ht hi => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hV'
    exact (hVP i).1
  · by_contra hno
    push Not at hno
    have hno' : ∀ i, ¬ SpectralAccumulation.IsoV V' (V i) := fun i => hno (V i) (Finset.mem_image_of_mem V (Finset.mem_univ i))
    have hG : G (Nat.findGreatest G (Module.finrank ℂ F) + 1) := by
      refine ⟨Fin.cons V' V, fun i => ?_, fun i j hij => ?_⟩
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
        · exact ⟨hd, ht, hi⟩
        · simpa only [Fin.cons_succ] using hVP i'
      · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
          rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
        · exact absurd rfl hij
        · simpa only [Fin.cons_zero, Fin.cons_succ] using hno' j'
        · simp only [Fin.cons_zero, Fin.cons_succ]
          exact fun h => hno' i' (isoV_symm (hVP i').1.stable h)
        · simp only [Fin.cons_succ]
          exact hVn i' j' (fun h => hij (by rw [h]))
    have := Nat.le_findGreatest (hbound _ hG) hG
    omega

end PositivityTheory.Rg.BcB.F.F5.Bo

end
