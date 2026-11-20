import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPsIrr

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi.OrdB
open GlobalTheory.PRep
section General
variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]
/- English proof (translation)
Establish `h : Commute (ρ t - c • (1 : Module.End ℂ V)) (ρ g)` using `Commute.sub_left ((Commute.all t g).map ρ) ((Commute.one_left _).smul_left c)`. Conclude with `LinearMap.congr_fun (h.pow_left m).eq v`.
-/
private theorem pow_comm (ρ : Representation ℂ G V) (t g : G) (c : ℂ) (m : ℕ) (v : V) :
    ((ρ t - c • (1 : Module.End ℂ V)) ^ m) (ρ g v) = ρ g (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) := by
  have h : Commute (ρ t - c • (1 : Module.End ℂ V)) (ρ g) :=
    Commute.sub_left ((Commute.all t g).map ρ) ((Commute.one_left _).smul_left c)
  exact LinearMap.congr_fun (h.pow_left m).eq v
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hv`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.sub_apply]`. Conclude with `sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)`.
-/
private theorem pow_mem (ρ : Representation ℂ G V) (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
    (v : V) (hv : v ∈ N.toSubmodule) : ((ρ t - c • (1 : Module.End ℂ V)) ^ m) v ∈ N.toSubmodule := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply]
    exact sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)
/- English proof (translation)
Use `haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1`. Take `⟨N, hN, hmax⟩` from `(wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule} ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩`. Use `⟨N, fun h => hN (by rw [h]; trivial), fun t c hc => ?_⟩` and prove the remaining obligations. Use `set f := ρ t - c • (1 : Module.End ℂ V) with hf`. Establish `hb : f x = 0` using `by simp [hf, hc]`.

Set `K : ℕ →o Subrepresentation ρ` to `⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by show (f ^ m) (ρ g v) ∈ N.toSubmodule`. Rewrite using `[hf, pow_comm]`. Conclude with `N.apply_mem_toSubmodule g hv⟩,`. Use `monotone_nat_of_le_succ fun m v hv => by show (f ^ (m + 1)) v ∈ N.toSubmodule`. Rewrite using `[add_comm, pow_add, Module.End.mul_apply]`.

Conclude with `pow_mem ρ N t _ 1 _ hv⟩`. Take `⟨a, ha⟩` from `WellFoundedGT.monotone_chain_condition K`. Set `R : Subrepresentation ρ` to `⟨N.toSubmodule ⊔ LinearMap.range (f ^ a), fun g v hv => by`. Take `⟨y, hy, _, ⟨z, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm]⟩⟩`. Establish `hR : x ∉ R.toSubmodule` using `fun hv => by`. Take `⟨y, hy, _, ⟨z, rfl⟩, h⟩` from `Submodule.mem_sup.1 hv`. Establish `h1 : z ∈ (K (1 + a)).toSubmodule` using `by show (f ^ (1 + a)) z ∈ N.toSubmodule`. Rewrite using `[pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, pow_one, hb, zero_sub, ← pow_one f]`.

Conclude with `neg_mem (pow_mem ρ N t _ 1 _ hy)`. Rewrite `h1` using `[← ha _ (by omega)]`. Conclude with `hN (h ▸ add_mem hy h1)`. Establish `hNR : N ≤ R` using `fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv`. Establish `hE : N = R`.

Assume the negation of the conclusion as `hne`. Conclude with `hmax R hR (lt_of_le_of_ne hNR hne)`. Use `⟨a, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hE]`. Conclude with `Submodule.mem_sup_right ⟨v, rfl⟩`.
-/
private theorem exists_nil {ρ : Representation ℂ G V} (hl : HasFiniteLength ρ) {x : V} (hx : x ≠ 0) :
    ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧ ∀ (t : G) (c : ℂ), ρ t x = c • x →
      ∃ m : ℕ, ∀ v, ((ρ t - c • (1 : Module.End ℂ V)) ^ m) v ∈ N.toSubmodule := by
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨N, hN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule}
    ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
  refine ⟨N, fun h => hN (by rw [h]; trivial), fun t c hc => ?_⟩
  set f := ρ t - c • (1 : Module.End ℂ V) with hf
  have hb : f x = 0 := by simp [hf, hc]
  let K : ℕ →o Subrepresentation ρ :=
    ⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by
        show (f ^ m) (ρ g v) ∈ N.toSubmodule
        rw [hf, pow_comm]
        exact N.apply_mem_toSubmodule g hv⟩,
      monotone_nat_of_le_succ fun m v hv => by
        show (f ^ (m + 1)) v ∈ N.toSubmodule
        rw [add_comm, pow_add, Module.End.mul_apply]
        exact pow_mem ρ N t _ 1 _ hv⟩
  obtain ⟨a, ha⟩ := WellFoundedGT.monotone_chain_condition K
  let R : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (f ^ a), fun g v hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm]⟩⟩
  have hR : x ∉ R.toSubmodule := fun hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, h⟩ := Submodule.mem_sup.1 hv
    have h1 : z ∈ (K (1 + a)).toSubmodule := by
      show (f ^ (1 + a)) z ∈ N.toSubmodule
      rw [pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, pow_one, hb, zero_sub, ← pow_one f]
      exact neg_mem (pow_mem ρ N t _ 1 _ hy)
    rw [← ha _ (by omega)] at h1
    exact hN (h ▸ add_mem hy h1)
  have hNR : N ≤ R := fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv
  have hE : N = R := by
    by_contra hne
    exact hmax R hR (lt_of_le_of_ne hNR hne)
  refine ⟨a, fun v => ?_⟩
  rw [hE]
  exact Submodule.mem_sup_right ⟨v, rfl⟩
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, pow_succ, mul_smul, sub_smul]`. Both sides reduce to the same expression.
-/
private theorem pow_eig {f : Module.End ℂ V} {v : V} {a : ℂ} (h : f v = a • v) (c : ℂ) (m : ℕ) :
    ((f - c • (1 : Module.End ℂ V)) ^ m) v = (a - c) ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, pow_succ, mul_smul, sub_smul]
    rfl
/- English proof (translation)
Take `⟨m, hm⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 hv`. Rewrite `hm` using `[pow_eig h]`. Conclude with `sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right h0)).1`.
-/
private theorem eq_of_gen {f : Module.End ℂ V} {v : V} {a c : ℂ} (h : f v = a • v) (h0 : v ≠ 0)
    (hv : v ∈ f.maxGenEigenspace c) : a = c := by
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv
  rw [pow_eig h] at hm
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((smul_eq_zero.1 hm).resolve_right h0)).1
/- English proof (translation)
Take `⟨S, ⟨hS0, hSE, hS⟩, hmin⟩` from `(wellFounded_lt (α := Submodule ℂ V)).has_min {S | S ≠ ⊥ ∧ S ≤ E ∧ ∀ t, ∀ v ∈ S, ρ t v ∈ S} ⟨E, hE0, le_rfl, hE⟩`. Establish `: Nontrivial S` using `Submodule.nontrivial_iff_ne_bot.2 hS0`. Establish `key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, ρ t v = c • v` using `fun t => by`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue ((ρ t).restrict (hS t))`. Take `⟨w, hw⟩` from `hc.exists_hasEigenvector`.

Establish `hw1 : ρ t w = c • (w : V)` using `congrArg Subtype.val hw.apply_eq_smul`. Use `⟨c, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1 : S ⊓ Module.End.eigenspace (ρ t) c = S`. Assume the negation of the conclusion as `hne`. Use `hmin _ ⟨?_, inf_le_left.trans hSE, ?_⟩ (lt_of_le_of_ne inf_le_left hne)` and prove the remaining obligations.

Conclude with `(Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, fun h => hw.2 (Subtype.ext h)⟩`. Introduce and unpack `s x ⟨hx, hx'⟩`. Use `⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]`. Rewrite `hv` using `[← h1]`.

Conclude with `Module.End.mem_eigenspace_iff.1 hv.2`. Use `choose c hc using key`. Take `⟨v, hv, hv0⟩` from `(Submodule.ne_bot_iff _).1 hS0`. Set `c' : G →* ℂ` to `{ toFun := c map_one' := by`. Use `hc 1 v hv` as an intermediate fact.

Rewrite `this` using `[map_one, Module.End.one_apply]`. Conclude with `smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)`. Use the proof step `map_mul' := fun s t => by`. Use `hc (s * t) v hv` as an intermediate fact. Rewrite `this` using `[map_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul, mul_comm]`.

Conclude with `smul_left_injective ℂ hv0 this.symm }`. Conclude with `⟨c'.toHomUnits, v, hSE hv, hv0, fun t => hc t v hv⟩`.
-/
private theorem exists_eig [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V) (hE0 : E ≠ ⊥)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) : ∃ χ : G →* ℂˣ, ∃ v ∈ E, v ≠ 0 ∧ ∀ t, ρ t v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hSE, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ V)).has_min
    {S | S ≠ ⊥ ∧ S ≤ E ∧ ∀ t, ∀ v ∈ S, ρ t v ∈ S} ⟨E, hE0, le_rfl, hE⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, ρ t v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((ρ t).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : ρ t w = c • (w : V) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (ρ t) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hSE, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : G →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul, mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  exact ⟨c'.toHomUnits, v, hSE hv, hv0, fun t => hc t v hv⟩
/- English proof (translation)
Rewrite using `[Submodule.eq_iSup_inf_genEigenspace (p := E) (f := ρ t) ⊤ (hE t) (Module.End.iSup_maxGenEigenspace_eq_top (ρ t))]`. Use `iSup_le fun c => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : E ⊓ Module.End.genEigenspace (ρ t) c ⊤ = ⊥`. Rewrite using `[h0]`. Conclude with `bot_le`.

Take `⟨χ, v, hv, hv0, hχ⟩` from `exists_eig ρ _ h0 fun s v hv => ⟨hE s v hv.1, by`. Take `⟨m, hm⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 hv.2`. Conclude with `(Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, by rw [pow_comm, hm, map_zero]⟩⟩`. Rewrite using `[← h χ v hv.1 hv0 hχ, eq_of_gen (hχ t) hv0 hv.2]`. Conclude with `inf_le_right`.
-/
private theorem le_gen [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (E : Submodule ℂ V)
    (hE : ∀ t, ∀ v ∈ E, ρ t v ∈ E) (μ : G →* ℂˣ)
    (h : ∀ χ : G →* ℂˣ, ∀ v ∈ E, v ≠ 0 → (∀ t, ρ t v = (χ t : ℂ) • v) → χ = μ) (t : G) :
    E ≤ Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) := by
  rw [Submodule.eq_iSup_inf_genEigenspace (p := E) (f := ρ t) ⊤ (hE t)
    (Module.End.iSup_maxGenEigenspace_eq_top (ρ t))]
  refine iSup_le fun c => ?_
  by_cases h0 : E ⊓ Module.End.genEigenspace (ρ t) c ⊤ = ⊥
  · rw [h0]; exact bot_le
  obtain ⟨χ, v, hv, hv0, hχ⟩ := exists_eig ρ _ h0 fun s v hv => ⟨hE s v hv.1, by
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hv.2
    exact (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨m, by rw [pow_comm, hm, map_zero]⟩⟩
  rw [← h χ v hv.1 hv0 hχ, eq_of_gen (hχ t) hv0 hv.2]
  exact inf_le_right
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]
/- English proof (translation)
Take `⟨T, hT, hnil⟩` from `exists_nil hl hx`. Use `haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1`. Take `⟨M, hM, hTM⟩` from `(eq_top_or_exists_le_coatom T).resolve_left hT`. Establish `hi` using `isIrreducible_subQuot hM.covBy_top`. Set `p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`.

Establish `hs : IsSmooth (subQuot ⊤ M)` using `IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ`. Take `⟨μ, hμ⟩` from `GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi`. Establish `hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule` using `fun g v => by`. Use `hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)` as an intermediate fact. Conclude with `(Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype) (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this`.

Establish `hM' : M.toSubmodule < ⊤` using `lt_top_iff_ne_top.2 fun h => hM.1 (Subrepresentation.toSubmodule_injective h)`. Take `⟨l, hl0, hlM⟩` from `Submodule.exists_le_ker_of_lt_top _ hM'`. Establish `hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v` using `fun g v => by`. Use `hlM (hμM g v)` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero]`. Then use the resulting hypothesis.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, l v ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `hl0 (LinearMap.ext hn)`. Use `⟨μ, ?_, fun t c hc => ?_, l, hl0, hle⟩` and prove the remaining obligations.

Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : ρ g v = v` using `hg`. Establish `h` using `hle g v`. Rewrite `h` using `[hg']`.

Conclude with `Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))`. Take `⟨m, hm⟩` from `hnil t c hc`. Establish `h1 : ∀ m : ℕ, l (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) = ((μ t : ℂ) - c) ^ m * l v` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => simp`.

Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, hle, LinearMap.smul_apply, Module.End.one_apply, map_smul, ih, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `hlM (hTM (hm v))`. Rewrite `h2` using `[LinearMap.mem_ker, h1]`.

Conclude with `sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1`.
-/
private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ)
    {x : V} (hx : x ≠ 0) : ∃ μ : G →* ℂˣ, IsSmoothChar μ ∧ (∀ (t : G) (c : ℂ), ρ t x = c • x → (μ t : ℂ) = c) ∧
      ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := by
  obtain ⟨T, hT, hnil⟩ := exists_nil hl hx
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨M, hM, hTM⟩ := (eq_top_or_exists_le_coatom T).resolve_left hT
  have hi := isIrreducible_subQuot hM.covBy_top
  let p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M) :=
    ⟨Submodule.mkQ _, fun _ => rfl⟩
  have hs : IsSmooth (subQuot ⊤ M) :=
    IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ
  obtain ⟨μ, hμ⟩ := GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi
  have hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule := fun g v => by
    have := hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)
    exact (Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype)
      (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this
  have hM' : M.toSubmodule < ⊤ := lt_top_iff_ne_top.2 fun h =>
    hM.1 (Subrepresentation.toSubmodule_injective h)
  obtain ⟨l, hl0, hlM⟩ := Submodule.exists_le_ker_of_lt_top _ hM'
  have hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v := fun g v => by
    have := hlM (hμM g v)
    rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this
  obtain ⟨v, hv⟩ : ∃ v, l v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hl0 (LinearMap.ext hn)
  refine ⟨μ, ?_, fun t c hc => ?_, l, hl0, hle⟩
  · refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : ρ g v = v := hg
    have h := hle g v
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))
  · obtain ⟨m, hm⟩ := hnil t c hc
    have h1 : ∀ m : ℕ, l (((ρ t - c • (1 : Module.End ℂ V)) ^ m) v) = ((μ t : ℂ) - c) ^ m * l v := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, map_sub, hle, LinearMap.smul_apply,
          Module.End.one_apply, map_smul, ih, smul_eq_mul]
        ring
    have h2 := hlM (hTM (hm v))
    rw [LinearMap.mem_ker, h1] at h2
    exact sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1
end General
section Abs
variable {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M) (c : ℕ)
  (φ : I.T →* ℂˣ)
/- English proof (translation)
Introduce `v hv g hg`. Take `⟨x, hx, t, ht, y, hy, rfl⟩` from `(iwMem G I c g).2.1.1 hg`. Establish `h` using `hv.2.2 ⟨t, I.Tc_le c ht⟩`. Rewrite `h` using `[hφ _ ht]`. Rewrite using `[map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv.2.1 y hy, h]`.

Simplify using `using hv.1 x hx`.
-/
private theorem eig_le (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) : I.eig π c φ ≤ fixd π (I.I1 c) := by
  intro v hv g hg
  obtain ⟨x, hx, t, ht, y, hy, rfl⟩ := (iwMem G I c g).2.1.1 hg
  have h := hv.2.2 ⟨t, I.Tc_le c ht⟩
  rw [hφ _ ht] at h
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hv.2.1 y hy, h]
  simpa using hv.1 x hx
/- English proof (translation)
Establish `st` using `((uOpLevel G I ℂ M π c).2.2 φ hφ).1`. Establish `key : ∀ (j : ℕ), ∀ w ∈ I.eig π c φ, I.uOp π a ((I.uOp π I.z ^ j) w) = (I.uOp π I.z ^ j) (I.uOp π a w)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro w _`.

Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `w hw`. Rewrite using `[pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (st _ I.z_mem w hw), (uOpMul G I ℂ M π _ _ ha I.z_mem w hw.1).2.1, (uOpMul G I ℂ M π _ _ I.z_mem ha w hw.1).2.1, I.comm a (I.P_le a ha) I.z (I.P_le _ I.z_mem)]`. Use `(Submodule.mem_iInf _).2 fun j => ?_` and prove the remaining obligations.

Take `⟨w, hw, rfl⟩` from `(Submodule.mem_iInf _).1 hv j`. Conclude with `⟨_, st a ha w hw, (key j w hw).symm⟩`.
-/
private theorem inv_stab (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) {a : G} (ha : a ∈ I.P) {v : M}
    (hv : v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j)) :
    I.uOp π a v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j) := by
  have st := ((uOpLevel G I ℂ M π c).2.2 φ hφ).1
  have key : ∀ (j : ℕ), ∀ w ∈ I.eig π c φ, I.uOp π a ((I.uOp π I.z ^ j) w) = (I.uOp π I.z ^ j) (I.uOp π a w) := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih _ (st _ I.z_mem w hw),
        (uOpMul G I ℂ M π _ _ ha I.z_mem w hw.1).2.1, (uOpMul G I ℂ M π _ _ I.z_mem ha w hw.1).2.1,
        I.comm a (I.P_le a ha) I.z (I.P_le _ I.z_mem)]
  refine (Submodule.mem_iInf _).2 fun j => ?_
  obtain ⟨w, hw, rfl⟩ := (Submodule.mem_iInf _).1 hv j
  exact ⟨_, st a ha w hw, (key j w hw).symm⟩
/- English proof (translation)
Establish `st` using `((uOpLevel G I ℂ M π c).2.2 φ hφ).1 _ I.z_mem`. Use `haveI : FiniteDimensional ℂ (I.eig π c φ) := Submodule.finiteDimensional_of_le (eig_le I π c φ hφ)`. Establish `hv0 : v ∈ I.eig π c φ` using `by simpa using (Submodule.mem_iInf _).1 hv 0`. Set `f : Module.End ℂ (I.eig π c φ)` to `(I.uOp π I.z).restrict st`. Establish `hf : ∀ (j : ℕ) (x : I.eig π c φ), ((f ^ j) x : M) = (I.uOp π I.z ^ j) x`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ j ih => intro x`.

Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]`. Both sides reduce to the same expression. Take `⟨m, hm⟩` from `(propCker G I ℂ M π hs v hv0.1).1 h0`. Establish `h1 : (⟨v, hv0⟩ : I.eig π c φ) ∈ ⨆ j : ℕ, LinearMap.ker (f ^ j)` using `Submodule.mem_iSup_of_mem m (Subtype.ext ((hf m _).trans hm))`. Establish `h2 : (⟨v, hv0⟩ : I.eig π c φ) ∈ ⨅ j : ℕ, LinearMap.range (f ^ j)`.

Use `(Submodule.mem_iInf _).2 fun j => ?_` and prove the remaining obligations. Take `⟨w, hw, e⟩` from `(Submodule.mem_iInf _).1 hv j`. Conclude with `⟨⟨w, hw⟩, Subtype.ext ((hf j _).trans e)⟩`. Conclude with `congrArg Subtype.val ((Submodule.disjoint_def.1 (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow f).disjoint) _ h1 h2)`.
-/
private theorem inv_inj (hφ : ∀ t : I.T, (t : G) ∈ I.Tc c → φ t = 1) (hs : I.Smooth π)
    [FiniteDimensional ℂ (fixd π (I.I1 c))] {v : M}
    (hv : v ∈ ⨅ j : ℕ, (I.eig π c φ).map (I.uOp π I.z ^ j)) (h0 : v ∈ I.jacKer π) : v = 0 := by
  have st := ((uOpLevel G I ℂ M π c).2.2 φ hφ).1 _ I.z_mem
  haveI : FiniteDimensional ℂ (I.eig π c φ) := Submodule.finiteDimensional_of_le (eig_le I π c φ hφ)
  have hv0 : v ∈ I.eig π c φ := by simpa using (Submodule.mem_iInf _).1 hv 0
  let f : Module.End ℂ (I.eig π c φ) := (I.uOp π I.z).restrict st
  have hf : ∀ (j : ℕ) (x : I.eig π c φ), ((f ^ j) x : M) = (I.uOp π I.z ^ j) x := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih => intro x; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl
  obtain ⟨m, hm⟩ := (propCker G I ℂ M π hs v hv0.1).1 h0
  have h1 : (⟨v, hv0⟩ : I.eig π c φ) ∈ ⨆ j : ℕ, LinearMap.ker (f ^ j) :=
    Submodule.mem_iSup_of_mem m (Subtype.ext ((hf m _).trans hm))
  have h2 : (⟨v, hv0⟩ : I.eig π c φ) ∈ ⨅ j : ℕ, LinearMap.range (f ^ j) := by
    refine (Submodule.mem_iInf _).2 fun j => ?_
    obtain ⟨w, hw, e⟩ := (Submodule.mem_iInf _).1 hv j
    exact ⟨⟨w, hw⟩, Subtype.ext ((hf j _).trans e)⟩
  exact congrArg Subtype.val
    ((Submodule.disjoint_def.1 (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow f).disjoint) _ h1 h2)
end Abs
section Num
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
/- English proof (translation)
Rewrite using `[torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)]`. Simplify using the standard rewrite rules.
-/
private theorem tc_single (ψ : Fin n → kˣ →* ℂˣ) (i : Fin n) (x : kˣ) : torusChar ψ (Pi.mulSingle i x) = ψ i x := by
  rw [torusChar_apply, Finset.prod_eq_single i (fun j _ hj => by simp [Pi.mulSingle_eq_of_ne hj]) (by simp)]
  simp
/- English proof (translation)
Establish `hd : ∀ (t : Fin n → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i` using `fun t => congrFun ((leviTorus k (Fin n)).left_inv t)`. Establish `hq : (Nat.card 𝓀[k] : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Establish `hn : ((nabs k (unif k) : ℝ) : ℂ) = (Nat.card 𝓀[k] : ℂ)⁻¹`. Rewrite using `[GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one GlAx.unif_spec]`. Simplify using `[resCard]`.

Establish `h1 : ∀ i : Fin n, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2) (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) * ((ω i * absPow k (((n : ℂ) - 1) / 2)) (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = (if (i : ℕ) < j then (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ …`. Introduce `i`. Use `split_ifs`. Rewrite using `[zpow_one, MonoidHom.mul_apply, Units.val_mul, mul_left_comm, ← Units.val_mul, ← MonoidHom.mul_apply, ← absPow_add, modExp_fin _ (fun _ => by simp), mul_assoc, val_absPow, hn, show ((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2 + ((n : ℂ) - 1) / 2) = (((n : ℤ) - 1 - (i : ℕ) : ℤ) : ℂ) …`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hp : ∀ (s : Finset (Fin n)) (e : Fin n → ℤ), ∏ i ∈ s, (Nat.card 𝓀[k] : ℂ) ^ e i = (Nat.card 𝓀[k] : ℂ) ^ ∑ i ∈ s, e i`. Introduce `s e`. Proceed by induction on `s using Finset.induction_on with`.

Consider the case `empty => simp`. Consider the case `insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]`. Establish `h2 : ∑ i : Fin n, (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) = -((j * (n - j) : ℕ) : ℤ)`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < j then -((n : ℤ) - 1 - 2 * i) else 0), ← Finset.sum_filter, show (Finset.range n).filter (· < j) = Finset.range j by ext; simp; omega, Nat.cast_mul, Nat.cast_sub hj]`. Use `clear h1`.

Generalize the expression as in `(n : ℤ) = N`. Use `clear hj`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [Finset.sum_range_succ, ih]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]`. Simplify using `only [hd, h1]`. Rewrite using `[Finset.prod_mul_distrib, hp, h2, psEig, Finset.prod_filter, Nat.cast_pow, _root_.zpow_neg, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts.
-/
private theorem num (ω : Fin n → kˣ →* ℂˣ) {j : ℕ} (hj : j ≤ n) :
    ((Nat.card 𝓀[k] ^ (j * (n - j)) : ℕ) : ℂ) *
      ((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
        (torusChar (fun i => ω i * absPow k (((n : ℂ) - 1) / 2))
          (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) = psEig ω j := by
  have hd : ∀ (t : Fin n → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t i) = t i := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have hq : (Nat.card 𝓀[k] : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : ((nabs k (unif k) : ℝ) : ℂ) = (Nat.card 𝓀[k] : ℂ)⁻¹ := by
    rw [GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one GlAx.unif_spec]
    simp [resCard]
  have h1 : ∀ i : Fin n, ((absPow k ((modExp (fun _ : Fin n => Unit) i : ℂ) / 2)
        (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ) *
      ((ω i * absPow k (((n : ℂ) - 1) / 2)) (unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) : ℂ)) =
      (if (i : ℕ) < j then (ω i (unif k) : ℂ) * ((Nat.card 𝓀[k] : ℂ) ^ (i : ℕ))⁻¹ else 1) *
        (Nat.card 𝓀[k] : ℂ) ^ (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) := by
    intro i
    split_ifs
    · rw [zpow_one, MonoidHom.mul_apply, Units.val_mul, mul_left_comm, ← Units.val_mul, ← MonoidHom.mul_apply,
        ← absPow_add, modExp_fin _ (fun _ => by simp), mul_assoc, val_absPow, hn,
        show ((((n : ℤ) - 1 - 2 * (i : ℕ) : ℤ) : ℂ) / 2 + ((n : ℂ) - 1) / 2) = (((n : ℤ) - 1 - (i : ℕ) : ℤ) : ℂ) by
          push_cast; ring, Complex.cpow_intCast, ← zpow_natCast, ← _root_.zpow_neg, ← zpow_add₀ hq, _root_.inv_zpow']
      congr 2
      ring
    · simp
  have hp : ∀ (s : Finset (Fin n)) (e : Fin n → ℤ),
      ∏ i ∈ s, (Nat.card 𝓀[k] : ℂ) ^ e i = (Nat.card 𝓀[k] : ℂ) ^ ∑ i ∈ s, e i := by
    intro s e
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ hq]
  have h2 : ∑ i : Fin n, (if (i : ℕ) < j then -((n : ℤ) - 1 - 2 * (i : ℕ)) else 0) = -((j * (n - j) : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i < j then -((n : ℤ) - 1 - 2 * i) else 0), ← Finset.sum_filter,
      show (Finset.range n).filter (· < j) = Finset.range j by ext; simp; omega, Nat.cast_mul, Nat.cast_sub hj]
    clear h1
    generalize (n : ℤ) = N
    clear hj
    induction j with
    | zero => simp
    | succ j ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [deltaHalf_apply, torusChar_apply, Units.coe_prod, Units.coe_prod, ← Finset.prod_mul_distrib]
  simp only [hd, h1]
  rw [Finset.prod_mul_distrib, hp, h2, psEig, Finset.prod_filter, Nat.cast_pow, _root_.zpow_neg, zpow_natCast]
  field_simp
end Num
end UpperTheory.V.Hi.OrdB
open GlobalTheory.PRep in
/- English proof (translation)
Introduce `H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 hD hne`. Take `⟨hker, hsm, hI, -, -, -, -, hidx, -, hT⟩` from `glBridge k n V π`. Establish `hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1` using `fun t ht => by`. Take `⟨y, hy, hy'⟩` from `hT t`. Establish `e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype`.

Rewrite using `[hy]`. Use `list_prod_mem fun x hx => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hx`. Conclude with `⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩`. Take `⟨s, hs, e⟩` from `e`.

Conclude with `(Subtype.ext e : s = t) ▸ hs`. Use `haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by`. Establish `hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c)`. Use extensionality with `v`. Conclude with `⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩`.

Rewrite using `[hfix]`. Conclude with `((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2`. Set `p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n))` to `Submodule.mkQ _`. Establish `hinj : ∀ v ∈ invPart π c φ, p v = 0 → v = 0` using `fun v hv h => OrdB.inv_inj _ π c φ hφ (hsm hπ) hv (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h)`. Establish `heig : invPart π c φ ≤ (glIwa k n).eig π c φ` using `fun v hv => by simpa using (Submodule.mem_iInf _).1 hv 0`.

Establish `hp : ∀ t v, jacB π t (p v) = (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) v)` using `fun t v => UnramFixed.jacB_apply π t _`. Set `E : Submodule ℂ (Jacquet π (unipB k (Fin n)))` to `⨅ (i : Fin n) (u : Uo k), Module.End.eigenspace (jacB π (Pi.mulSingle i (u : kˣ))) (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ)`. Establish `hE : ∀ y, y ∈ E ↔ ∀ (i : Fin n) (u : Uo k), jacB π (Pi.mulSingle i (u : kˣ)) y = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • y` using `fun y => by`. Simplify using `only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]`. Establish `hEs : ∀ t, ∀ y ∈ E, jacB π t y ∈ E` using `fun t y hy => (hE _).2 fun i u => by`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, (hE _).1 hy, map_smul]`. Establish `hpE : ∀ v ∈ invPart π c φ, p v ∈ E` using `fun v hv => (hE _).2 fun i u => by`. Establish `hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n)` using `fun j => by`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Rewrite using `[Pi.mulSingle_eq_same]`. Conclude with `u.2`. Simplify using `[Pi.mulSingle_eq_of_ne h]`. Rewrite using `[hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]`. Conclude with `congrArg p ((heig hv).2.2 (eT k n i u))`.

Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hne`. Establish `hl : HasFiniteLength (jacB π)` using `(hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2 ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))`. Use `haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k`. Take `⟨μ, hμs, hμ, l, hl0, hle⟩` from `OrdB.exists_form (isSmooth_jacB hπ) hl fun h => hx0 (hinj x hx h)`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by`.

Use `⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i), fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩` and prove the remaining obligations. Rewrite using `[torusChar_apply]`. Use `conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]`. Both sides reduce to the same expression. Establish `hsq : IsSubquotient π (prinSeries ψ)` using `GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle`.

Establish `hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹` using `fun i u => by`. Rewrite using `[← OrdB.tc_single]`. Conclude with `Units.ext (hμ _ _ ((hE _).1 (hpE x hx) i u))`. Take `⟨hfd, -, hmult⟩` from `UpperTheory.V.AlgebraTools.jqMult H.loc.geo H.loc.bz k n V π ψ hπ hψ hsq`. Establish `hw : ∀ w : Equiv.Perm (Fin n), (∀ i (u : Uo k), ψ (w i) u = ψ i u) → w = 1` using `fun w h => by`.

Use `Equiv.ext fun i => by_contra fun hi => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `hD _ _ hi`. Conclude with `hu (inv_injective ((hψφ _ u).symm.trans ((h i u).trans (hψφ i u))))`. Establish `hgen : E ≤ ⨅ t, Module.End.maxGenEigenspace (jacB π t) (torusChar ψ t : ℂ)`. Use `le_iInf (OrdB.le_gen _ E hEs _ fun χ y hy hy0 hχ => ?_)` and prove the remaining obligations.

Establish `h1 : (⨅ t, Module.End.maxGenEigenspace (jacB π t) (χ t : ℂ) : Submodule ℂ _) ≠ ⊥` using `(Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun t => (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [OrdB.pow_eig (hχ t)]; simp⟩, hy0⟩`. Establish `h2` using `(Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h)).trans_le (hmult χ)`. Take `⟨⟨w, rfl⟩⟩` from `(Nat.card_pos_iff.1 h2).1`. Rewrite using `[hw w fun i u => ?_]`. Both sides reduce to the same expression.

Establish `h3` using `(hχ _).symm.trans ((hE _).1 hy i u)`. Rewrite `h3` using `[OrdB.tc_single, ← hψφ]`. Conclude with `Units.ext (smul_left_injective ℂ hy0 h3)`. Establish `hE1 : Module.finrank ℂ E ≤ 1`. Use `(Submodule.finrank_mono hgen).trans ((hmult _).trans ?_)` and prove the remaining obligations.

Establish `key : ∀ a : {w : Equiv.Perm (Fin n) // torusChar ψ = torusChar (ψ ∘ w)}, a.1 = 1` using `fun a => hw _ fun i u => by`. Use `DFunLike.congr_fun a.2 (Pi.mulSingle i (u : kˣ))` as an intermediate fact. Rewrite `this` using `[OrdB.tc_single, OrdB.tc_single]`. Conclude with `this.symm`. Conclude with `Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩`.

Establish `hact : ∀ t, ∀ y ∈ E, jacB π t y = (torusChar ψ t : ℂ) • y` using `fun t y hy => by`. Distinguish the cases in `hy0 : y = 0`. Simplify using `[hy0]`. Establish `hy1 : (⟨y, hy⟩ : E) ≠ 0` using `fun h => hy0 (congrArg Subtype.val h)`. Establish `: Nontrivial E` using `nontrivial_of_ne _ _ hy1`.

Take `⟨a, ha⟩` from `(finrank_eq_one_iff_of_nonzero' _ hy1).1 (le_antisymm hE1 Module.finrank_pos) ⟨_, hEs t y hy⟩`. Establish `ha' : jacB π t y = a • y` using `(congrArg Subtype.val ha).symm`. Rewrite using `[ha', OrdB.eq_of_gen ha' hy0 ((Submodule.mem_iInf _).1 (hgen hy) t)]`. Take `⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ` from `⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩`. Establish `hω : ∀ i, IsSmoothChar (ω i)` using `fun i => by`.

Use `(hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))` as an intermediate fact. Rewrite `this` using `[absPow_neg, mul_inv_cancel_right]`. Then use the resulting hypothesis. Establish `hinv : IsInvOn φ ω` using `fun i u => by`. Use `hψφ i u` as an intermediate fact. Rewrite `this` using `[MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one]`.

Rewrite using `[this, inv_inv]`. Use `⟨ω, hω, hinv, (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient H k n ω hω fun i j hij => ?_).2 V π hirr hsq, le_antisymm ?_ ?_, fun v hv j hj => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hD i j hij`. Rewrite `hu` using `[hinv, hinv]`. Use `⟨fun h => hu (by rw [h]), fun h => hu ?_⟩` and prove the remaining obligations.

Rewrite using `[h, MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one]`. Use `le_trans (LinearMap.finrank_le_finrank_of_injective (f := p.restrict hpE) ?_) hE1` and prove the remaining obligations. Conclude with `(injective_iff_map_eq_zero _).2 fun v h => Subtype.ext (hinj v v.2 (congrArg Subtype.val h))`. Use `haveI : FiniteDimensional ℂ (invPart π c φ) := Submodule.finiteDimensional_of_le (heig.trans (OrdB.eig_le _ π c φ hφ))`. Conclude with `Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)`.

Rewrite using `[← sub_eq_zero]`. Use `hinj _ (sub_mem (OrdB.inv_stab _ π c φ hφ (al_mem k n j) hv) (Submodule.smul_mem _ _ hv)) ?_` and prove the remaining obligations. Establish `h1` using `propCp _ (glIwa k n) ℂ V π _ (al_mem k n j) v (heig hv).1`. Rewrite `h1` using `[hker, hidx j hj]`. Establish `h2 : p _ = 0` using `(Submodule.Quotient.mk_eq_zero _).2 h1`.

Establish `h3` using `(hp (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) v).symm.trans (hact _ _ (hpE v hv))`. Rewrite `h3` using `[← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul]`. Rewrite `h2`, the goal using `[map_sub, map_smul, sub_eq_zero]`. Rewrite using `[h2, ← OrdB.num ω hj, mul_smul, ← h3]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Hi.exists_principal_series_of_distinct_inv_ne_bot :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), GlobalTheory.PRep.IsSmooth π → π.IsIrreducible → ∀ (c : ℕ) (φ : (glIwa k n).T →* ℂˣ), (∀ i (y : Uo k), (y : kˣ) ∈ Uc k (c + 1) → φ (eT k n i y) = 1) → Distinct φ → invPart π c φ ≠ ⊥ → ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsInvOn φ ω ∧ Nonempty (π.Equiv (PS ω)) ∧ Module.finrank ℂ (invPart π c φ) = 1 ∧ ∀ v ∈ invPart π c φ, ∀ j ≤ n, (glIwa k n).uOp π (al k n j) v = psEig ω j • v := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 hD hne
  obtain ⟨hker, hsm, hI, -, -, -, -, hidx, -, hT⟩ := glBridge k n V π
  have hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1 := fun t ht => by
    obtain ⟨y, hy, hy'⟩ := hT t
    have e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype := by
      rw [hy]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact ⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩
    obtain ⟨s, hs, e⟩ := e
    exact (Subtype.ext e : s = t) ▸ hs
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by
    have hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c) := by
      ext v
      exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
    rw [hfix]
    exact ((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hinj : ∀ v ∈ invPart π c φ, p v = 0 → v = 0 := fun v hv h =>
    OrdB.inv_inj _ π c φ hφ (hsm hπ) hv (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h)
  have heig : invPart π c φ ≤ (glIwa k n).eig π c φ := fun v hv => by simpa using (Submodule.mem_iInf _).1 hv 0
  have hp : ∀ t v, jacB π t (p v) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) v) :=
    fun t v => UnramFixed.jacB_apply π t _
  let E : Submodule ℂ (Jacquet π (unipB k (Fin n))) :=
    ⨅ (i : Fin n) (u : Uo k), Module.End.eigenspace (jacB π (Pi.mulSingle i (u : kˣ))) (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ)
  have hE : ∀ y, y ∈ E ↔ ∀ (i : Fin n) (u : Uo k),
      jacB π (Pi.mulSingle i (u : kˣ)) y = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • y := fun y => by
    simp only [E, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hEs : ∀ t, ∀ y ∈ E, jacB π t y ∈ E := fun t y hy => (hE _).2 fun i u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, (hE _).1 hy, map_smul]
  have hpE : ∀ v ∈ invPart π c φ, p v ∈ E := fun v hv => (hE _).2 fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
    exact congrArg p ((heig hv).2.2 (eT k n i u))
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := OrdB.exists_form (isSmooth_jacB hπ) hl fun h => hx0 (hinj x hx h)
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    rw [← OrdB.tc_single]
    exact Units.ext (hμ _ _ ((hE _).1 (hpE x hx) i u))
  obtain ⟨hfd, -, hmult⟩ := UpperTheory.V.AlgebraTools.jqMult H.loc.geo H.loc.bz k n V π ψ hπ hψ hsq
  have hw : ∀ w : Equiv.Perm (Fin n), (∀ i (u : Uo k), ψ (w i) u = ψ i u) → w = 1 := fun w h => by
    refine Equiv.ext fun i => by_contra fun hi => ?_
    obtain ⟨u, hu⟩ := hD _ _ hi
    exact hu (inv_injective ((hψφ _ u).symm.trans ((h i u).trans (hψφ i u))))
  have hgen : E ≤ ⨅ t, Module.End.maxGenEigenspace (jacB π t) (torusChar ψ t : ℂ) := by
    refine le_iInf (OrdB.le_gen _ E hEs _ fun χ y hy hy0 hχ => ?_)
    have h1 : (⨅ t, Module.End.maxGenEigenspace (jacB π t) (χ t : ℂ) : Submodule ℂ _) ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨y, (Submodule.mem_iInf _).2 fun t =>
        (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [OrdB.pow_eig (hχ t)]; simp⟩, hy0⟩
    have h2 := (Nat.pos_of_ne_zero fun h => h1 (Submodule.finrank_eq_zero.1 h)).trans_le (hmult χ)
    obtain ⟨⟨w, rfl⟩⟩ := (Nat.card_pos_iff.1 h2).1
    rw [hw w fun i u => ?_]
    · rfl
    have h3 := (hχ _).symm.trans ((hE _).1 hy i u)
    rw [OrdB.tc_single, ← hψφ] at h3
    exact Units.ext (smul_left_injective ℂ hy0 h3)
  have hE1 : Module.finrank ℂ E ≤ 1 := by
    refine (Submodule.finrank_mono hgen).trans ((hmult _).trans ?_)
    have key : ∀ a : {w : Equiv.Perm (Fin n) // torusChar ψ = torusChar (ψ ∘ w)}, a.1 = 1 := fun a =>
      hw _ fun i u => by
        have := DFunLike.congr_fun a.2 (Pi.mulSingle i (u : kˣ))
        rw [OrdB.tc_single, OrdB.tc_single] at this
        exact this.symm
    exact Finite.card_le_one_iff_subsingleton.2 ⟨fun a b => Subtype.ext ((key a).trans (key b).symm)⟩
  have hact : ∀ t, ∀ y ∈ E, jacB π t y = (torusChar ψ t : ℂ) • y := fun t y hy => by
    by_cases hy0 : y = 0
    · simp [hy0]
    have hy1 : (⟨y, hy⟩ : E) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
    have : Nontrivial E := nontrivial_of_ne _ _ hy1
    obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hy1).1 (le_antisymm hE1 Module.finrank_pos) ⟨_, hEs t y hy⟩
    have ha' : jacB π t y = a • y := (congrArg Subtype.val ha).symm
    rw [ha', OrdB.eq_of_gen ha' hy0 ((Submodule.mem_iInf _).1 (hgen hy) t)]
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  refine ⟨ω, hω, hinv, (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient H k n ω hω fun i j hij => ?_).2 V π hirr hsq, le_antisymm ?_ ?_, fun v hv j hj => ?_⟩
  · obtain ⟨u, hu⟩ := hD i j hij
    rw [hinv, hinv] at hu
    refine ⟨fun h => hu (by rw [h]), fun h => hu ?_⟩
    rw [h, MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one]
  · refine le_trans (LinearMap.finrank_le_finrank_of_injective (f := p.restrict hpE) ?_) hE1
    exact (injective_iff_map_eq_zero _).2 fun v h => Subtype.ext (hinj v v.2 (congrArg Subtype.val h))
  · haveI : FiniteDimensional ℂ (invPart π c φ) :=
      Submodule.finiteDimensional_of_le (heig.trans (OrdB.eig_le _ π c φ hφ))
    exact Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.1 h)
  · rw [← sub_eq_zero]
    refine hinj _ (sub_mem (OrdB.inv_stab _ π c φ hφ (al_mem k n j) hv) (Submodule.smul_mem _ _ hv)) ?_
    have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n j) v (heig hv).1
    rw [hker, hidx j hj] at h1
    have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
    have h3 := (hp (fun i => unif k ^ (if (i : ℕ) < j then 1 else 0 : ℤ)) v).symm.trans (hact _ _ (hpE v hv))
    rw [← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul] at h3
    rw [map_sub, map_smul, sub_eq_zero] at h2 ⊢
    rw [h2, ← OrdB.num ω hj, mul_smul, ← h3]
    rfl
end
