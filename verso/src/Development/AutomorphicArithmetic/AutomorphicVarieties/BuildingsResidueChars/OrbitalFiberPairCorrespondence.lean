import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberDecomposition
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberPushforward
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberOfBot

open MulAction UpperTheory.V.Z.Sym

private structure PairSp (H G : Type) [Group G] (U : Subgroup G) : Type where
  fst : H
  snd : G ⧸ U

@[instance_reducible] private def pairAct {H G : Type} [Group H] [Group G] (j : H →* G) (U : Subgroup G) :
    MulAction H (PairSp H G U) where
  smul h p := ⟨h * p.1 * h⁻¹, j h • p.2⟩
  one_smul p := by
    show (⟨(1 : H) * p.1 * (1 : H)⁻¹, j 1 • p.2⟩ : PairSp H G U) = p
    simp
  mul_smul a b p := by
    show (⟨a * b * p.1 * (a * b)⁻¹, j (a * b) • p.2⟩ : PairSp H G U) =
      ⟨a * (b * p.1 * b⁻¹) * a⁻¹, j a • j b • p.2⟩
    simp [mul_assoc, mul_smul]

/- English proof (translation)
Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul U g`. Conclude with `⟨h, h.2, hh⟩`.
-/
private theorem out_eq_mul {G : Type} [Group G] (U : Subgroup G) (g : G) :
    ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨h, h.2, hh⟩

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem pair_inv_mul_eq_of_mul_self_eq_one {H G : Type} [Group H] [Group G] (a b o u : G) (key : a⁻¹ * (b * a) = b) :
    (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * (o⁻¹ * b * o) * u := by
  calc (a * o * u)⁻¹ * b * (a * o * u) = u⁻¹ * o⁻¹ * (a⁻¹ * (b * a)) * o * u := by group
    _ = u⁻¹ * (o⁻¹ * b * o) * u := by rw [key]; group

/- English proof (translation)
Introduce `H G I _ _ j H₀ U c f δ Hi _ φ hcen hfix hc hf hfin hT hidx hrange hδ hcov`. Use `letI : MulAction H (PairSp H G U) := pairAct j U`. Use `letI : MulAction H (G ⧸ U) := MulAction.compHom (G ⧸ U) j`. Use `letI : ∀ i, MulAction (Hi i) (G ⧸ U) := fun i => MulAction.compHom (G ⧸ U) (j.comp (φ i))`. Establish `hnorm : H₀.Normal` using `⟨fun n hn g => by`.

Establish `hc'` using `Subgroup.mem_center_iff.1 (hcen hn) g`. Rewrite using `[hc', mul_inv_cancel_right]`. Conclude with `hn⟩`. Establish `hout : ∀ (a : G) (y : G ⧸ U), ∃ u ∈ U, ((a • y : G ⧸ U).out) = a * y.out * u`. Introduce `a y`.

Establish `hy : (a • y : G ⧸ U) = ((a * y.out : G) : G ⧸ U)` using `by conv_lhs => rw [← QuotientGroup.out_eq' y]`. Both sides reduce to the same expression. Rewrite using `[hy]`. Conclude with `out_eq_mul U _`. Set `K' : PairSp H G U → ℂ` to `fun p => c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)`.

Establish `hKinv : ∀ (h : H) (p : PairSp H G U), K' (h • p) = K' p`. Introduce `h p`. Take `⟨u, hu, he⟩` from `hout (j h) p.2`. Use `show c (h * p.1 * h⁻¹) * f ((j h • p.2).out⁻¹ * j (h * p.1 * h⁻¹) * (j h • p.2).out) = c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)`. Rewrite using `[hc, he, map_mul, map_mul, map_inv]`.

Use `congr 1`. Rewrite using `[show (j h * p.2.out * u)⁻¹ * (j h * j p.1 * (j h)⁻¹) * (j h * p.2.out * u) = u⁻¹ * (p.2.out⁻¹ * j p.1 * p.2.out) * u by group]`. Conclude with `hf u hu _`. Establish `hfib : ∀ x : G ⧸ U, {p : PairSp H G U | p.2 = x ∧ K' p ≠ 0}.Finite`. Introduce `x`.

Use `((hfin x.out).image (fun γ => (⟨γ, x⟩ : PairSp H G U))).subset ?_` and prove the remaining obligations. Introduce and unpack `⟨γ, y⟩ ⟨hy, hne⟩`. Express the relevant statement in the definitionally equal form `y = x at hy`. Substitute `hy` using the available equality. Conclude with `⟨γ, hne, rfl⟩`.

Take `⟨T, hTc⟩` from `hT`. Establish `hT'fin : (⋃ s ∈ T, {p : PairSp H G U | p.2 = (s : G ⧸ U) ∧ K' p ≠ 0}).Finite` using `Set.Finite.biUnion T.finite_toSet (fun s _ => hfib _)`. Establish `hcoverP : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ h : H, ∃ s ∈ hT'fin.toFinset, p = h • s`. Introduce `p hp`. Take `⟨γ0, s, hs, u, hu, he⟩` from `hTc p.2.out`.

Use `⟨γ0, γ0⁻¹ • p, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_iUnion₂]`. Use `⟨s, hs, ?_, ?_⟩` and prove the remaining obligations. Use `show j γ0⁻¹ • p.2 = (s : G ⧸ U) conv_lhs => rw [← QuotientGroup.out_eq' p.2, he] show ((j γ0⁻¹ * (j γ0 * s * u) : G) : G ⧸ U) = s`. Rewrite using `[QuotientGroup.eq, map_inv]`.

Simplify `U.inv_mem hu` using `[mul_assoc]`. Rewrite using `[hKinv]`. Conclude with `hp`. Rewrite using `[smul_smul, mul_inv_cancel, one_smul]`. Establish `hfixP : ∀ z ∈ H₀, ∀ p : PairSp H G U, z • p = p`.

Introduce `z hz p`. Take `⟨γ, y⟩` from `p`. Use `show (⟨z * γ * z⁻¹, j z • y⟩ : PairSp H G U) = ⟨γ, y⟩`. Rewrite using `[← Subgroup.mem_center_iff.1 (hcen hz) γ, mul_inv_cancel_right, hfix z hz y]`. Establish `hpush` using `UpperTheory.orbitalFiber_pushforward H (PairSp H G U) (G ⧸ U) H₀ (fun p => p.2) K' hnorm (fun _ _ => rfl) hfixP hKinv ⟨hT'fin.toFinset, hcoverP⟩ hfib (fun p _ => hidx p.2)`.

Establish `hfibsum : ∀ x : G ⧸ U, (∑ᶠ (p : PairSp H G U) (_ : p.2 = x), K' p) = ∑ᶠ γ : H, c γ * f (x.out⁻¹ * j γ * x.out)`. Introduce `x`. Establish `hr : ∀ p : PairSp H G U, (p.2 = x) = (p ∈ Set.range (fun γ : H => (⟨γ, x⟩ : PairSp H G U)))`. Introduce `p`. Apply `propext` to reduce the goal to its premises.

Prove the components needed by the constructor for the conclusion. Introduce `hp`. Conclude with `⟨p.1, by rw [← hp]⟩`. Introduce and unpack `⟨γ, rfl⟩`. Both sides reduce to the same expression.

Simplify using `only [hr]`. Rewrite using `[finsum_mem_range (fun a b hab => congrArg PairSp.fst hab)]`. Establish `hcomm : ∀ i (a : Hi i), φ i a * δ i * (φ i a)⁻¹ = δ i`. Introduce `i a`. Rewrite using `[(hrange i (φ i a)).1 ⟨a, rfl⟩, mul_inv_cancel_right]`.

Establish `hequi : ∀ i (a : Hi i) (y : G ⧸ U), (⟨δ i, a • y⟩ : PairSp H G U) = φ i a • (⟨δ i, y⟩ : PairSp H G U)`. Introduce `i a y`. Use `show (⟨δ i, j (φ i a) • y⟩ : PairSp H G U) = ⟨φ i a * δ i * (φ i a)⁻¹, j (φ i a) • y⟩`. Rewrite using `[hcomm]`. Establish `hkiinv : ∀ i (a : Hi i) (y : G ⧸ U), c (δ i) * f ((a • y).out⁻¹ * j (δ i) * (a • y).out) = c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)`.

Introduce `i a y`. Take `⟨u, hu, he⟩` from `hout (j (φ i a)) y`. Use `show c (δ i) * f ((j (φ i a) • y).out⁻¹ * j (δ i) * (j (φ i a) • y).out) = _`. Rewrite using `[he, pair_inv_mul_eq_of_mul_self_eq_one (H := H) _ _ _ _ ?_, hf u hu]`. Establish `h1` using `(hrange i (φ i a)).1 ⟨a, rfl⟩`.

Rewrite using `[← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_left]`. Establish `hcovD : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ i, ∃ y : G ⧸ U, ∃ h : H, c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 ∧ p = h • (⟨δ i, y⟩ : PairSp H G U)`. Introduce and unpack `⟨γ, y⟩ hp`. Take `⟨i, h, hγ⟩` from `hcov γ y.out hp`. Use `⟨i, j h⁻¹ • y, h, ?_, ?_⟩` and prove the remaining obligations.

Establish `h2` using `hKinv h⁻¹ ⟨γ, y⟩`. Establish `h3 : h⁻¹ * γ * h⁻¹⁻¹ = δ i` using `by rw [hγ]; group`. Express the relevant statement in the definitionally equal form `c (h⁻¹ * γ * h⁻¹⁻¹) * f ((j h⁻¹ • y).out⁻¹ * j (h⁻¹ * γ * h⁻¹⁻¹) * (j h⁻¹ • y).out) = K' ⟨γ, y⟩ at h2`. Rewrite `h2` using `[h3]`. Rewrite using `[h2]`.

Conclude with `hp`. Use `show (⟨γ, y⟩ : PairSp H G U) = ⟨h * δ i * h⁻¹, j h • j h⁻¹ • y⟩`. Rewrite using `[← hγ, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]`. Establish `huniq : ∀ (i i' : I) (y y' : G ⧸ U) (h : H), c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 → c (δ i') * f (y'.out⁻¹ * j (δ i') * y'.out) ≠ 0 → h • (⟨δ i, y⟩ : PairSp H G U) = ⟨δ i', y'⟩ → i = i' ∧ h ∈ (φ i).range`. Introduce `i i' y y' h _ _ he`.

Establish `h1 : h * δ i * h⁻¹ = δ i'` using `congrArg PairSp.fst he`. Establish `hii` using `hδ i i' h h1.symm`. Substitute `hii` using the available equality. Use `⟨rfl, (hrange i h).2 ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hdec` using `UpperTheory.orbitalFiber_decomposition H (PairSp H G U) I H₀ K' Hi (fun _ => G ⧸ U) φ (fun i y => (⟨δ i, y⟩ : PairSp H G U)) (fun i y => c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)) hnorm hKinv ⟨hT'fin.toFinset, hcoverP⟩ hequi (fun _ _ _ hab => congrArg PairSp.snd hab) hkiinv (fun _ …`. Use `show gq H₀ (fun y : G ⧸ U => ∑ᶠ γ : H, c γ * f (y.out⁻¹ * j γ * y.out)) = _`. Simplify using `only [← hfibsum]`. Rewrite using `[← hpush, hdec]`. Apply `finsum_congr` to reduce the goal to its premises.

Introduce `i`. Conclude with `(UpperTheory.orbitalFiber_of_bot (Hi i) (G ⧸ U) (Subgroup.comap (φ i) H₀) (fun y => f (y.out⁻¹ * j (δ i) * y.out))).1 (c (δ i))`.
-/
theorem UpperTheory.orbitalFiber_pair_correspondence :
    UpperTheory.V.Z.Sym.Glob.Fib.Pair := by
  classical
  intro H G I _ _ j H₀ U c f δ Hi _ φ hcen hfix hc hf hfin hT hidx hrange hδ hcov
  letI : MulAction H (PairSp H G U) := pairAct j U
  letI : MulAction H (G ⧸ U) := MulAction.compHom (G ⧸ U) j
  letI : ∀ i, MulAction (Hi i) (G ⧸ U) := fun i => MulAction.compHom (G ⧸ U) (j.comp (φ i))
  have hnorm : H₀.Normal := ⟨fun n hn g => by
    have hc' := Subgroup.mem_center_iff.1 (hcen hn) g
    rw [hc', mul_inv_cancel_right]
    exact hn⟩
  have hout : ∀ (a : G) (y : G ⧸ U), ∃ u ∈ U, ((a • y : G ⧸ U).out) = a * y.out * u := by
    intro a y
    have hy : (a • y : G ⧸ U) = ((a * y.out : G) : G ⧸ U) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [hy]
    exact out_eq_mul U _
  let K' : PairSp H G U → ℂ := fun p => c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
  have hKinv : ∀ (h : H) (p : PairSp H G U), K' (h • p) = K' p := by
    intro h p
    obtain ⟨u, hu, he⟩ := hout (j h) p.2
    show c (h * p.1 * h⁻¹) * f ((j h • p.2).out⁻¹ * j (h * p.1 * h⁻¹) * (j h • p.2).out) =
      c p.1 * f (p.2.out⁻¹ * j p.1 * p.2.out)
    rw [hc, he, map_mul, map_mul, map_inv]
    congr 1
    rw [show (j h * p.2.out * u)⁻¹ * (j h * j p.1 * (j h)⁻¹) * (j h * p.2.out * u) =
        u⁻¹ * (p.2.out⁻¹ * j p.1 * p.2.out) * u by group]
    exact hf u hu _
  have hfib : ∀ x : G ⧸ U, {p : PairSp H G U | p.2 = x ∧ K' p ≠ 0}.Finite := by
    intro x
    refine ((hfin x.out).image (fun γ => (⟨γ, x⟩ : PairSp H G U))).subset ?_
    rintro ⟨γ, y⟩ ⟨hy, hne⟩
    change y = x at hy
    subst hy
    exact ⟨γ, hne, rfl⟩
  obtain ⟨T, hTc⟩ := hT
  have hT'fin : (⋃ s ∈ T, {p : PairSp H G U | p.2 = (s : G ⧸ U) ∧ K' p ≠ 0}).Finite :=
    Set.Finite.biUnion T.finite_toSet (fun s _ => hfib _)
  have hcoverP : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ h : H, ∃ s ∈ hT'fin.toFinset, p = h • s := by
    intro p hp
    obtain ⟨γ0, s, hs, u, hu, he⟩ := hTc p.2.out
    refine ⟨γ0, γ0⁻¹ • p, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Set.mem_iUnion₂]
      refine ⟨s, hs, ?_, ?_⟩
      · show j γ0⁻¹ • p.2 = (s : G ⧸ U)
        conv_lhs => rw [← QuotientGroup.out_eq' p.2, he]
        show ((j γ0⁻¹ * (j γ0 * s * u) : G) : G ⧸ U) = s
        rw [QuotientGroup.eq, map_inv]
        simpa [mul_assoc] using U.inv_mem hu
      · rw [hKinv]
        exact hp
    · rw [smul_smul, mul_inv_cancel, one_smul]
  have hfixP : ∀ z ∈ H₀, ∀ p : PairSp H G U, z • p = p := by
    intro z hz p
    obtain ⟨γ, y⟩ := p
    show (⟨z * γ * z⁻¹, j z • y⟩ : PairSp H G U) = ⟨γ, y⟩
    rw [← Subgroup.mem_center_iff.1 (hcen hz) γ, mul_inv_cancel_right, hfix z hz y]
  have hpush := UpperTheory.orbitalFiber_pushforward H (PairSp H G U) (G ⧸ U) H₀ (fun p => p.2) K' hnorm
    (fun _ _ => rfl) hfixP hKinv ⟨hT'fin.toFinset, hcoverP⟩ hfib (fun p _ => hidx p.2)
  have hfibsum : ∀ x : G ⧸ U, (∑ᶠ (p : PairSp H G U) (_ : p.2 = x), K' p) =
      ∑ᶠ γ : H, c γ * f (x.out⁻¹ * j γ * x.out) := by
    intro x
    have hr : ∀ p : PairSp H G U,
        (p.2 = x) = (p ∈ Set.range (fun γ : H => (⟨γ, x⟩ : PairSp H G U))) := by
      intro p
      apply propext
      constructor
      · intro hp
        exact ⟨p.1, by rw [← hp]⟩
      · rintro ⟨γ, rfl⟩
        rfl
    simp only [hr]
    rw [finsum_mem_range (fun a b hab => congrArg PairSp.fst hab)]
  have hcomm : ∀ i (a : Hi i), φ i a * δ i * (φ i a)⁻¹ = δ i := by
    intro i a
    rw [(hrange i (φ i a)).1 ⟨a, rfl⟩, mul_inv_cancel_right]
  have hequi : ∀ i (a : Hi i) (y : G ⧸ U),
      (⟨δ i, a • y⟩ : PairSp H G U) = φ i a • (⟨δ i, y⟩ : PairSp H G U) := by
    intro i a y
    show (⟨δ i, j (φ i a) • y⟩ : PairSp H G U) = ⟨φ i a * δ i * (φ i a)⁻¹, j (φ i a) • y⟩
    rw [hcomm]
  have hkiinv : ∀ i (a : Hi i) (y : G ⧸ U),
      c (δ i) * f ((a • y).out⁻¹ * j (δ i) * (a • y).out) = c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) := by
    intro i a y
    obtain ⟨u, hu, he⟩ := hout (j (φ i a)) y
    show c (δ i) * f ((j (φ i a) • y).out⁻¹ * j (δ i) * (j (φ i a) • y).out) = _
    rw [he, pair_inv_mul_eq_of_mul_self_eq_one (H := H) _ _ _ _ ?_, hf u hu]
    have h1 := (hrange i (φ i a)).1 ⟨a, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul, ← h1, inv_mul_cancel_left]
  have hcovD : ∀ p : PairSp H G U, K' p ≠ 0 → ∃ i, ∃ y : G ⧸ U, ∃ h : H,
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 ∧ p = h • (⟨δ i, y⟩ : PairSp H G U) := by
    rintro ⟨γ, y⟩ hp
    obtain ⟨i, h, hγ⟩ := hcov γ y.out hp
    refine ⟨i, j h⁻¹ • y, h, ?_, ?_⟩
    · have h2 := hKinv h⁻¹ ⟨γ, y⟩
      have h3 : h⁻¹ * γ * h⁻¹⁻¹ = δ i := by rw [hγ]; group
      change c (h⁻¹ * γ * h⁻¹⁻¹) * f ((j h⁻¹ • y).out⁻¹ * j (h⁻¹ * γ * h⁻¹⁻¹) * (j h⁻¹ • y).out) =
        K' ⟨γ, y⟩ at h2
      rw [h3] at h2
      rw [h2]
      exact hp
    · show (⟨γ, y⟩ : PairSp H G U) = ⟨h * δ i * h⁻¹, j h • j h⁻¹ • y⟩
      rw [← hγ, smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  have huniq : ∀ (i i' : I) (y y' : G ⧸ U) (h : H),
      c (δ i) * f (y.out⁻¹ * j (δ i) * y.out) ≠ 0 → c (δ i') * f (y'.out⁻¹ * j (δ i') * y'.out) ≠ 0 →
      h • (⟨δ i, y⟩ : PairSp H G U) = ⟨δ i', y'⟩ → i = i' ∧ h ∈ (φ i).range := by
    intro i i' y y' h _ _ he
    have h1 : h * δ i * h⁻¹ = δ i' := congrArg PairSp.fst he
    have hii := hδ i i' h h1.symm
    subst hii
    refine ⟨rfl, (hrange i h).2 ?_⟩
    calc h * δ i = h * δ i * h⁻¹ * h := by group
      _ = δ i * h := by rw [h1]
  have hdec := UpperTheory.orbitalFiber_decomposition H (PairSp H G U) I H₀ K' Hi (fun _ => G ⧸ U) φ
    (fun i y => (⟨δ i, y⟩ : PairSp H G U))
    (fun i y => c (δ i) * f (y.out⁻¹ * j (δ i) * y.out)) hnorm hKinv ⟨hT'fin.toFinset, hcoverP⟩
    hequi (fun _ _ _ hab => congrArg PairSp.snd hab) hkiinv (fun _ _ _ => rfl) hcovD huniq
  show gq H₀ (fun y : G ⧸ U => ∑ᶠ γ : H, c γ * f (y.out⁻¹ * j γ * y.out)) = _
  simp only [← hfibsum]
  rw [← hpush, hdec]
  apply finsum_congr
  intro i
  exact (UpperTheory.orbitalFiber_of_bot (Hi i) (G ⧸ U) (Subgroup.comap (φ i) H₀)
    (fun y => f (y.out⁻¹ * j (δ i) * y.out))).1 (c (δ i))
