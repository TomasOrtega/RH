import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private noncomputable def redMap {l : ℕ} [Fact l.Prime] {X Y : Type} [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y]
    [Module ℤ_[l] Y] (f : X →ₗ[ℤ_[l]] Y) (m : ℕ) : (X ⧸ lSub l X m) →ₗ[ℤ_[l]] (Y ⧸ lSub l Y m) :=
  Submodule.mapQ _ _ f fun x hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨f y, (map_smul _ _ _).symm⟩

/- English proof (translation)
Use `haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Establish `hs : Function.Surjective (PadicInt.toZModPow (p` using `l) k) := fun z => by`. Take `⟨a, rfl⟩` from `ZMod.natCast_zmod_surjective z`. Conclude with `⟨a, map_natCast _ a⟩`. Rewrite using `[← PadicInt.ker_toZModPow, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv, Nat.card_zmod]`.
-/
private theorem card_quotient_eq_card_of_isReps (l : ℕ) [Fact l.Prime] (k : ℕ) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ k}) = l ^ k := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hs : Function.Surjective (PadicInt.toZModPow (p := l) k) := fun z => by
    obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective z
    exact ⟨a, map_natCast _ a⟩
  rw [← PadicInt.ker_toZModPow, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv,
    Nat.card_zmod]

/- English proof (translation)
Establish `h : Ideal.span {q} = Ideal.span {(l : ℤ_[l]) ^ q.valuation}`. Rewrite using `[Ideal.span_singleton_eq_span_singleton]`. Use `Associated.symm ⟨PadicInt.unitCoeff hq, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `(PadicInt.unitCoeff_spec hq).symm`.

Rewrite using `[h]`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises. Rewrite using `[card_quotient_eq_card_of_isReps]`. Conclude with `pow_ne_zero _ (Fact.out : l.Prime).ne_zero`.
-/
private theorem finite_padicInt_quot_span_of_ne_zero (l : ℕ) [Fact l.Prime] {q : ℤ_[l]} (hq : q ≠ 0) :
    Finite (ℤ_[l] ⧸ Ideal.span {q}) := by
  have h : Ideal.span {q} = Ideal.span {(l : ℤ_[l]) ^ q.valuation} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hq, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hq).symm
  rw [h]
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient_eq_card_of_isReps]
  exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero

/- English proof (translation)
Set `I : Ideal ℤ_[l]` to `Ideal.span {(l : ℤ_[l]) ^ m}`. Set `φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l] ⧸ I)` to `LinearMap.pi (fun i => (Submodule.mkQ I) ∘ₗ LinearMap.proj i)`. Establish `hsurj : Function.Surjective φ`. Introduce `g`. Use `choose y hy using fun i => Submodule.Quotient.mk_surjective I (g i)`.

Conclude with `⟨y, funext fun i => hy i⟩`. Establish `hker : LinearMap.ker φ = lSub l (Fin n → ℤ_[l]) m`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_ker, mem_lSub]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `h2 : ∀ i, ∃ y, (l : ℤ_[l]) ^ m * y = x i` using `fun i => by`. Establish `h1 : (Submodule.Quotient.mk (x i) : ℤ_[l] ⧸ I) = 0` using `congrFun hx i`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']`. Take `⟨a, ha⟩` from `h1`.

Conclude with `⟨a, by rw [mul_comm]; exact ha⟩`. Use `choose y hy using h2`. Conclude with `⟨y, funext fun i => by simp [hy]⟩`. Introduce and unpack `⟨y, rfl⟩`. Use function extensionality and compare the values at `i`.

Use `show (Submodule.Quotient.mk _ : ℤ_[l] ⧸ I) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']`. Conclude with `⟨y i, by simp [mul_comm]⟩`. Rewrite using `[← hker, Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_fun, card_quotient_eq_card_of_isReps, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]`.
-/
private theorem card_pi_padicInt_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ m}
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l] ⧸ I) :=
    LinearMap.pi (fun i => (Submodule.mkQ I) ∘ₗ LinearMap.proj i)
  have hsurj : Function.Surjective φ := by
    intro g
    choose y hy using fun i => Submodule.Quotient.mk_surjective I (g i)
    exact ⟨y, funext fun i => hy i⟩
  have hker : LinearMap.ker φ = lSub l (Fin n → ℤ_[l]) m := by
    ext x
    rw [LinearMap.mem_ker, mem_lSub]
    constructor
    · intro hx
      have h2 : ∀ i, ∃ y, (l : ℤ_[l]) ^ m * y = x i := fun i => by
        have h1 : (Submodule.Quotient.mk (x i) : ℤ_[l] ⧸ I) = 0 := congrFun hx i
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h1
        obtain ⟨a, ha⟩ := h1
        exact ⟨a, by rw [mul_comm]; exact ha⟩
      choose y hy using h2
      exact ⟨y, funext fun i => by simp [hy]⟩
    · rintro ⟨y, rfl⟩
      funext i
      show (Submodule.Quotient.mk _ : ℤ_[l] ⧸ I) = 0
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
      exact ⟨y i, by simp [mul_comm]⟩
  rw [← hker, Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_fun,
    card_quotient_eq_card_of_isReps, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

/- English proof (translation)
Introduce `l _ N _ _ _`. Take `⟨n, ι, _, p, hp, e, ⟨f⟩⟩` from `Module.equiv_free_prod_directSum ℤ_[l] N`. Use `set D := DirectSum ι fun i => ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i with hD`. Set `g : N ≃ₗ[ℤ_[l]] (Fin n → ℤ_[l]) × D` to `f.trans (LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ_[l] ℤ_[l] (Fin n)) (LinearEquiv.refl _ _))`. Use `haveI : Finite D := by haveI : ∀ i, Finite (ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i) := fun i => finite_padicInt_quot_span_of_ne_zero l (pow_ne_zero _ (hp i).ne_zero)`.

Conclude with `Finite.of_injective _ (DirectSum.linearEquivFunOnFintype ℤ_[l] ι _).injective`. Establish `hrank : finrank ℤ_[l] N = n`. Apply `Module.finrank_eq_of_rank_eq` to reduce the goal to its premises. Establish `h0 : Module.rank ℤ_[l] D = 0`. Rewrite using `[rank_eq_zero_iff]`.

Introduce `x`. Use `⟨(Nat.card D : ℤ_[l]), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]`. Conclude with `card_nsmul_eq_zero'`. Rewrite using `[g.rank_eq, ← LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ_[l] (Fin n → ℤ_[l]) D), LinearMap.range_eq_top.2 LinearMap.fst_surjective, rank_top, LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, h0, add_zero, rank_fun', Fintype.card_fin]`.

Rewrite using `[hrank]`. Use `⟨Nat.card D, fun m _ => ?_⟩` and prove the remaining obligations. Set `f1 : N →ₗ[ℤ_[l]] (Fin n → ℤ_[l])` to `LinearMap.fst _ _ _ ∘ₗ g.toLinearMap`. Set `f2 : N →ₗ[ℤ_[l]] D` to `LinearMap.snd _ _ _ ∘ₗ g.toLinearMap`. Set `Ψ` to `LinearMap.prod (redMap f1 m) (redMap f2 m)`.

Establish `hinj : Function.Injective Ψ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `q hq`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Establish `e1 : (Submodule.Quotient.mk (f1 x) : (Fin n → ℤ_[l]) ⧸ lSub l _ m) = 0` using `congrArg Prod.fst hq`.

Establish `e2 : (Submodule.Quotient.mk (f2 x) : D ⧸ lSub l D m) = 0` using `congrArg Prod.snd hq`. Rewrite `e1`, `e2` using `[Submodule.Quotient.mk_eq_zero, mem_lSub]`. Take `⟨y1, hy1⟩` from `e1`. Take `⟨y2, hy2⟩` from `e2`. Rewrite using `[Submodule.Quotient.mk_eq_zero, mem_lSub]`.

Use `⟨g.symm (y1, y2), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul, Prod.smul_mk, hy1, hy2]`. Simplify using `[f1, f2]`. Establish `hF` using `card_pi_padicInt_quot_lSub l n m`. Use `haveI : Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`.

Use `haveI : Finite (D ⧸ lSub l D m) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)`. Use `haveI : Finite (N ⧸ lSub l N m) := Finite.of_injective _ hinj`. Establish `hsurj : Function.Surjective (redMap f1 m)`. Introduce `q`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Use `⟨Submodule.Quotient.mk (g.symm (y, 0)), ?_⟩` and prove the remaining obligations. Simplify using `[redMap, f1]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← hF]`. Conclude with `Nat.card_le_card_of_surjective _ hsurj`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.card_quotient_powSubmodule_grows_finrank :
    ∀ (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [Module.Finite ℤ_[l] N], Grows l (fun m => Nat.card (N ⧸ lSub l N m)) (finrank ℤ_[l] N) := by
  intro l _ N _ _ _
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum ℤ_[l] N
  set D := DirectSum ι fun i => ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i with hD
  let g : N ≃ₗ[ℤ_[l]] (Fin n → ℤ_[l]) × D :=
    f.trans (LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ_[l] ℤ_[l] (Fin n))
      (LinearEquiv.refl _ _))
  haveI : Finite D := by
    haveI : ∀ i, Finite (ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i) := fun i =>
      finite_padicInt_quot_span_of_ne_zero l (pow_ne_zero _ (hp i).ne_zero)
    exact Finite.of_injective _ (DirectSum.linearEquivFunOnFintype ℤ_[l] ι _).injective
  have hrank : finrank ℤ_[l] N = n := by
    apply Module.finrank_eq_of_rank_eq
    have h0 : Module.rank ℤ_[l] D = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card D : ℤ_[l]), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      exact card_nsmul_eq_zero'
    rw [g.rank_eq, ← LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ_[l] (Fin n → ℤ_[l]) D),
      LinearMap.range_eq_top.2 LinearMap.fst_surjective, rank_top, LinearMap.ker_fst,
      rank_range_of_injective _ LinearMap.inr_injective, h0, add_zero, rank_fun', Fintype.card_fin]
  rw [hrank]
  refine ⟨Nat.card D, fun m _ => ?_⟩
  let f1 : N →ₗ[ℤ_[l]] (Fin n → ℤ_[l]) := LinearMap.fst _ _ _ ∘ₗ g.toLinearMap
  let f2 : N →ₗ[ℤ_[l]] D := LinearMap.snd _ _ _ ∘ₗ g.toLinearMap
  let Ψ := LinearMap.prod (redMap f1 m) (redMap f2 m)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e1 : (Submodule.Quotient.mk (f1 x) : (Fin n → ℤ_[l]) ⧸ lSub l _ m) = 0 :=
      congrArg Prod.fst hq
    have e2 : (Submodule.Quotient.mk (f2 x) : D ⧸ lSub l D m) = 0 := congrArg Prod.snd hq
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub] at e1 e2
    obtain ⟨y1, hy1⟩ := e1
    obtain ⟨y2, hy2⟩ := e2
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub]
    refine ⟨g.symm (y1, y2), ?_⟩
    rw [← map_smul, Prod.smul_mk, hy1, hy2]
    simp [f1, f2]
  have hF := card_pi_padicInt_quot_lSub l n m
  haveI : Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  haveI : Finite (D ⧸ lSub l D m) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Finite (N ⧸ lSub l N m) := Finite.of_injective _ hinj
  have hsurj : Function.Surjective (redMap f1 m) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨Submodule.Quotient.mk (g.symm (y, 0)), ?_⟩
    simp [redMap, f1]
  constructor
  · rw [← hF]
    exact Nat.card_le_card_of_surjective _ hsurj
  · calc Nat.card (N ⧸ lSub l N m)
        ≤ Nat.card (((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) × (D ⧸ lSub l D m)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = l ^ (m * n) * Nat.card (D ⧸ lSub l D m) := by rw [Nat.card_prod, hF]
      _ ≤ l ^ (m * n) * Nat.card D :=
          Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ (Submodule.Quotient.mk_surjective _))
      _ ≤ l ^ (m * n) * l ^ (Nat.card D) :=
          Nat.mul_le_mul_left _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
      _ = l ^ (m * n + Nat.card D) := (pow_add _ _ _).symm
