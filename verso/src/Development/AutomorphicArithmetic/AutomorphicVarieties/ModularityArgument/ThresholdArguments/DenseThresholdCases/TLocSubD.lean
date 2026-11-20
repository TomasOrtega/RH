import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.LocSubD
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
section General
variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]
/- English proof (translation)
Establish `h : Commute (ρ t - algebraMap ℂ (Module.End ℂ V) c) (ρ g)` using `Commute.sub_left ((Commute.all t g).map ρ) (Algebra.commutes c (ρ g))`. Conclude with `LinearMap.congr_fun (h.pow_left m).eq v`.
-/
private theorem pow_comm_rep (ρ : Representation ℂ G V) (t g : G) (c : ℂ) (m : ℕ) (v : V) :
    ((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) (ρ g v) =
      ρ g (((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) v) := by
  have h : Commute (ρ t - algebraMap ℂ (Module.End ℂ V) c) (ρ g) :=
    Commute.sub_left ((Commute.all t g).map ρ) (Algebra.commutes c (ρ g))
  exact LinearMap.congr_fun (h.pow_left m).eq v
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hv`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]`. Conclude with `sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)`.
-/
private theorem pow_mem_sub (ρ : Representation ℂ G V) (N : Subrepresentation ρ) (t : G) (c : ℂ) (m : ℕ)
    (v : V) (hv : v ∈ N.toSubmodule) : ((ρ t - algebraMap ℂ (Module.End ℂ V) c) ^ m) v ∈ N.toSubmodule := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact sub_mem (N.apply_mem_toSubmodule t ih) (N.toSubmodule.smul_mem c ih)
/- English proof (translation)
Use `haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1`. Take `⟨N, hN, hmax⟩` from `(wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule} ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩`. Use `⟨N, fun h => hN (by rw [h]; trivial), fun t => ?_⟩` and prove the remaining obligations. Use `set f := ρ t - algebraMap ℂ (Module.End ℂ V) (c t) with hf`. Set `K : ℕ →o Subrepresentation ρ` to `⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by show (f ^ m) (ρ g v) ∈ N.toSubmodule`.

Rewrite using `[hf, pow_comm_rep]`. Conclude with `N.apply_mem_toSubmodule g hv⟩,`. Use `monotone_nat_of_le_succ fun m v hv => by show (f ^ (m + 1)) v ∈ N.toSubmodule`. Rewrite using `[add_comm, pow_add, Module.End.mul_apply]`. Conclude with `pow_mem_sub ρ N t _ 1 _ hv⟩`.

Take `⟨a, ha⟩` from `WellFoundedGT.monotone_chain_condition K`. Take `⟨b, hb⟩` from `hxc t`. Set `R : Subrepresentation ρ` to `⟨N.toSubmodule ⊔ LinearMap.range (f ^ (a + b)), fun g v hv => by`. Take `⟨y, hy, _, ⟨z, rfl⟩, rfl⟩` from `Submodule.mem_sup.1 hv`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm_rep]⟩⟩`. Establish `hR : x ∉ R.toSubmodule` using `fun hv => by`. Take `⟨y, hy, _, ⟨z, rfl⟩, h⟩` from `Submodule.mem_sup.1 hv`. Establish `h1 : z ∈ (K (b + (a + b))).toSubmodule` using `by show (f ^ (b + (a + b))) z ∈ N.toSubmodule`. Rewrite using `[pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, hb, zero_sub]`.

Conclude with `neg_mem (pow_mem_sub ρ N t _ b _ hy)`. Rewrite `h1` using `[← ha _ (by omega), ha (a + b) (by omega)]`. Conclude with `hN (h ▸ add_mem hy h1)`. Establish `hNR : N ≤ R` using `fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv`. Establish `hE : N = R`.

Assume the negation of the conclusion as `hne`. Conclude with `hmax R hR (lt_of_le_of_ne hNR hne)`. Use `⟨a + b, fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[hE]`. Conclude with `Submodule.mem_sup_right ⟨v, rfl⟩`.
-/
private theorem exists_nil {ρ : Representation ℂ G V} (hl : HasFiniteLength ρ) {c : G → ℂ} {x : V} (hx : x ≠ 0)
    (hxc : ∀ t, ∃ m : ℕ, ((ρ t - algebraMap ℂ (Module.End ℂ V) (c t)) ^ m) x = 0) :
    ∃ N : Subrepresentation ρ, N ≠ ⊤ ∧
      ∀ t, ∃ m : ℕ, ∀ v, ((ρ t - algebraMap ℂ (Module.End ℂ V) (c t)) ^ m) v ∈ N.toSubmodule := by
  haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1
  obtain ⟨N, hN, hmax⟩ := (wellFounded_gt (α := Subrepresentation ρ)).has_min {N | x ∉ N.toSubmodule}
    ⟨⊥, fun h => hx ((Submodule.mem_bot ℂ).1 h)⟩
  refine ⟨N, fun h => hN (by rw [h]; trivial), fun t => ?_⟩
  set f := ρ t - algebraMap ℂ (Module.End ℂ V) (c t) with hf
  let K : ℕ →o Subrepresentation ρ :=
    ⟨fun m => ⟨N.toSubmodule.comap (f ^ m), fun g v hv => by
        show (f ^ m) (ρ g v) ∈ N.toSubmodule
        rw [hf, pow_comm_rep]
        exact N.apply_mem_toSubmodule g hv⟩,
      monotone_nat_of_le_succ fun m v hv => by
        show (f ^ (m + 1)) v ∈ N.toSubmodule
        rw [add_comm, pow_add, Module.End.mul_apply]
        exact pow_mem_sub ρ N t _ 1 _ hv⟩
  obtain ⟨a, ha⟩ := WellFoundedGT.monotone_chain_condition K
  obtain ⟨b, hb⟩ := hxc t
  let R : Subrepresentation ρ := ⟨N.toSubmodule ⊔ LinearMap.range (f ^ (a + b)), fun g v hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hv
    rw [map_add]
    exact Submodule.add_mem_sup (N.apply_mem_toSubmodule g hy) ⟨ρ g z, by rw [hf, pow_comm_rep]⟩⟩
  have hR : x ∉ R.toSubmodule := fun hv => by
    obtain ⟨y, hy, _, ⟨z, rfl⟩, h⟩ := Submodule.mem_sup.1 hv
    have h1 : z ∈ (K (b + (a + b))).toSubmodule := by
      show (f ^ (b + (a + b))) z ∈ N.toSubmodule
      rw [pow_add, Module.End.mul_apply, eq_sub_of_add_eq' h, map_sub, hb, zero_sub]
      exact neg_mem (pow_mem_sub ρ N t _ b _ hy)
    rw [← ha _ (by omega), ha (a + b) (by omega)] at h1
    exact hN (h ▸ add_mem hy h1)
  have hNR : N ≤ R := fun v hv => Submodule.mem_sup_left (S := N.toSubmodule) hv
  have hE : N = R := by
    by_contra hne
    exact hmax R hR (lt_of_le_of_ne hNR hne)
  refine ⟨a + b, fun v => ?_⟩
  rw [hE]
  exact Submodule.mem_sup_right ⟨v, rfl⟩
variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]
/- English proof (translation)
Take `⟨T, hT, hnil⟩` from `exists_nil hl hx hxc`. Use `haveI := ((hasFiniteLength_iff_wellFounded ρ).1 hl).1`. Take `⟨M, hM, hTM⟩` from `(eq_top_or_exists_le_coatom T).resolve_left hT`. Establish `hi` using `isIrreducible_subQuot hM.covBy_top`. Set `p : (⊤ : Subrepresentation ρ).toRepresentation.IntertwiningMap (subQuot ⊤ M)` to `⟨Submodule.mkQ _, fun _ => rfl⟩`.

Establish `hs : IsSmooth (subQuot ⊤ M)` using `IsSubquotient.isSmooth ⟨⊤, p, Submodule.Quotient.mk_surjective _⟩ hρ`. Take `⟨μ, hμ⟩` from `GlobalTheory.TorusEigenform.exists_char_of_isIrreducible hs hi`. Establish `hμM : ∀ g v, ρ g v - (μ g : ℂ) • v ∈ M.toSubmodule` using `fun g v => by`. Use `hμ g (Submodule.Quotient.mk ⟨v, trivial⟩)` as an intermediate fact. Conclude with `(Submodule.Quotient.eq (M.toSubmodule.comap (⊤ : Subrepresentation ρ).toSubmodule.subtype) (x := ⟨ρ g v, trivial⟩) (y := ⟨(μ g : ℂ) • v, trivial⟩)).1 this`.

Establish `hM' : M.toSubmodule < ⊤` using `lt_top_iff_ne_top.2 fun h => hM.1 (Subrepresentation.toSubmodule_injective h)`. Take `⟨l, hl0, hlM⟩` from `Submodule.exists_le_ker_of_lt_top _ hM'`. Establish `hle : ∀ g v, l (ρ g v) = (μ g : ℂ) * l v` using `fun g v => by`. Use `hlM (hμM g v)` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero]`. Then use the resulting hypothesis.

Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, l v ≠ 0 := by`. Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Conclude with `hl0 (LinearMap.ext hn)`. Establish `hμχ : μ = χ` using `MonoidHom.ext fun t => by`.

Take `⟨m, hm⟩` from `hnil t`. Establish `h1 : ∀ m : ℕ, l (((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) v) = ((μ t : ℂ) - χ t) ^ m * l v` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`.

Rewrite using `[pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, hle, map_smul, ih, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `hlM (hTM (hm v))`. Rewrite `h2` using `[LinearMap.mem_ker, h1]`. Conclude with `Units.ext (sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1)`.

Substitute `hμχ` using the available equality. Use `⟨?_, l, hl0, hle⟩` and prove the remaining obligations. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : ρ g v = v` using `hg`.

Establish `h` using `hle g v`. Rewrite `h` using `[hg']`. Conclude with `Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))`.
-/
private theorem exists_form {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (hl : HasFiniteLength ρ) {χ : G →* ℂˣ}
    {x : V} (hx : x ≠ 0)
    (hxc : ∀ t, ∃ m : ℕ, ((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) x = 0) :
    IsSmoothChar χ ∧ ∃ l : V →ₗ[ℂ] ℂ, l ≠ 0 ∧ ∀ g v, l (ρ g v) = (χ g : ℂ) * l v := by
  obtain ⟨T, hT, hnil⟩ := exists_nil hl hx hxc
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
  have hμχ : μ = χ := MonoidHom.ext fun t => by
    obtain ⟨m, hm⟩ := hnil t
    have h1 : ∀ m : ℕ, l (((ρ t - algebraMap ℂ (Module.End ℂ V) (χ t : ℂ)) ^ m) v) =
        ((μ t : ℂ) - χ t) ^ m * l v := fun m => by
      induction m with
      | zero => simp
      | succ m ih =>
        rw [pow_succ', Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply, map_sub, hle,
          map_smul, ih, smul_eq_mul]
        ring
    have h2 := hlM (hTM (hm v))
    rw [LinearMap.mem_ker, h1] at h2
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff'.1 ((mul_eq_zero.1 h2).resolve_right hv)).1)
  subst hμχ
  refine ⟨?_, l, hl0, hle⟩
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset ((hρ v).mem_nhds (by simp)) ?_)
  intro g hg
  have hg' : ρ g v = v := hg
  have h := hle g v
  rw [hg'] at h
  exact Units.ext (mul_right_cancel₀ hv (h.symm.trans (one_mul _).symm))
end General
/- English proof (translation)
The claim follows from `smul_right_injective M hc h`.
-/
private theorem smul_cancel {M : Type} [AddCommGroup M] [Module ℂ M] {c : ℂ} (hc : c ≠ 0) {a b : M}
    (h : c • a = c • b) : a = b :=
  smul_right_injective M hc h
/- English proof (translation)
The claim follows from `GroupWithZero.toNontrivial`.
-/
private theorem val_nontrivial {k : Type} [Field k] [ValuativeRel k] : Nontrivial (ValueGroupWithZero k) :=
  GroupWithZero.toNontrivial
attribute [local instance] val_nontrivial
section Lev
open GlobalTheory.IwahoriInj GlobalTheory.IwahoriTraceProof
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
/- English proof (translation)
Introduce `i j hij`. Establish `hj` using `j.2`. Establish `hij' : (i : ℕ) < j` using `hij`. Establish `e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1))` using `by omega`. Establish `hc0 : 0 < valuation k (c : k)` using `zero_lt_iff.2 ((valuation k).ne_zero_iff.2 c.ne_zero)`.

Use `beta_reduce`. Rewrite using `[e]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]`. Rewrite using `[← mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc]`. Conclude with `mul_le_of_le_one_right' (pow_le_one' h1 _)`. Use `_ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) := mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)`.
-/
private theorem sdom_of_step {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (s : Fin n → kˣ) (c : kˣ)
    (h1 : valuation k (c : k) ≤ 1)
    (h2 : ∀ i j : Fin n, i < j → valuation k (s i : k) * valuation k (c : k) < valuation k (s j : k)) :
    Sig.SDom fun i : Fin n => s i * c ^ (n - (i : ℕ)) := by
  intro i j hij
  have hj := j.2
  have hij' : (i : ℕ) < j := hij
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  have hc0 : 0 < valuation k (c : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 c.ne_zero)
  beta_reduce
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  calc valuation k (s i : k) * valuation k (c : k) *
        (valuation k (c : k) ^ (n - (j : ℕ)) * valuation k (c : k) ^ ((j : ℕ) - i - 1))
      ≤ valuation k (s i : k) * valuation k (c : k) * valuation k (c : k) ^ (n - (j : ℕ)) := by
        rw [← mul_assoc]
        exact mul_le_of_le_one_right' (pow_le_one' h1 _)
    _ < valuation k (s j : k) * valuation k (c : k) ^ (n - (j : ℕ)) :=
        mul_lt_mul_of_pos_right (h2 i j hij) (pow_pos hc0 _)
/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin n) with h | h` into its components or cases. Conclude with `⟨1, fun i => h.elim i, fun i => h.elim i⟩`. Take `⟨p, hp⟩` from `Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))`. Take `⟨x, q, hq, hx⟩` from `UpperTheory.V.AlgebraTools.exists_isUnif (k := k)`. Establish `hx1 : valuation k (x : k) < 1`.

Establish `h0 : valuation k (q : k) ≤ 1` using `q.2`. Establish `hne : valuation k (q : k) ≠ 1` using `fun h => hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)`. Rewrite using `[← hx]`. Conclude with `lt_of_le_of_ne h0 hne`. Use `set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀`.

Establish `hc1 : valuation k (c₀ : k) ≤ 1` using `by simpa using hp (p.1, p.1)`. Establish `hcx : valuation k ((c₀ * x : kˣ) : k) < 1`. Rewrite using `[Units.val_mul, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1`. Use `⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩` and prove the remaining obligations.

Simplify `hcx` using `using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa`. Use `sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_` and prove the remaining obligations. Establish `hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k)`. Use `(mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← map_mul, ← Units.val_mul]`.

Use `congr 2`. Simplify using the standard rewrite rules. Establish `hj0 : 0 < valuation k (t j : k)` using `zero_lt_iff.2 ((valuation k).ne_zero_iff.2 (t j).ne_zero)`. Rewrite using `[Units.val_mul, map_mul, ← mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exists_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ d : Fin n → kˣ, Sig.SDom d ∧ Sig.SDom (t * d) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun i => h.elim i, fun i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min
    (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  obtain ⟨x, q, hq, hx⟩ := UpperTheory.V.AlgebraTools.exists_isUnif (k := k)
  have hx1 : valuation k (x : k) < 1 := by
    have h0 : valuation k (q : k) ≤ 1 := q.2
    have hne : valuation k (q : k) ≠ 1 := fun h =>
      hq.not_isUnit ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one.2 h)
    rw [← hx]
    exact lt_of_le_of_ne h0 hne
  set c₀ : kˣ := t p.2 * (t p.1)⁻¹ with hc₀
  have hc1 : valuation k (c₀ : k) ≤ 1 := by simpa using hp (p.1, p.1)
  have hcx : valuation k ((c₀ * x : kˣ) : k) < 1 := by
    rw [Units.val_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc1) hx1
  refine ⟨fun i => (c₀ * x) ^ (n - (i : ℕ)), ?_, ?_⟩
  · simpa using sdom_of_step (1 : Fin n → kˣ) (c₀ * x) hcx.le fun i j _ => by simpa using hcx
  · refine sdom_of_step t (c₀ * x) hcx.le fun i j _ => ?_
    have hle : valuation k (t i : k) * valuation k (c₀ : k) ≤ valuation k (t j : k) := by
      refine (mul_le_mul_right (hp (i, j)) (valuation k (t i : k))).trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
    have hj0 : 0 < valuation k (t j : k) := zero_lt_iff.2 ((valuation k).ne_zero_iff.2 (t j).ne_zero)
    rw [Units.val_mul, map_mul, ← mul_assoc]
    calc valuation k (t i : k) * valuation k (c₀ : k) * valuation k (x : k)
        ≤ valuation k (t j : k) * valuation k (x : k) := mul_le_mul_left hle _
      _ < valuation k (t j : k) * 1 := mul_lt_mul_of_pos_left hx1 hj0
      _ = valuation k (t j : k) := mul_one _
/- English proof (translation)
Introduce `i j hij`. Simplify using `only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]`. Use `zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le ?_` and prove the remaining obligations. Establish `: ((i : ℕ) : ℤ) ≤ (j : ℕ)` using `by exact_mod_cast Fin.le_def.1 hij`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem jqInj_dom {x : kˣ} (hx : valuation k (x : k) = uniformizer k) (m : ℕ) :
    Dom fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))) := by
  intro i j hij
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
  refine zpow_le_zpow_right_of_le_one₀ unif_pos uniformizer_lt_one.le ?_
  have : ((i : ℕ) : ℤ) ≤ (j : ℕ) := by exact_mod_cast Fin.le_def.1 hij
  nlinarith
/- English proof (translation)
Establish `key : ∀ u ∈ unipB k (Fin n), ∀ᶠ m : ℕ in Filter.atTop, GlobalTheory.StepData.IntM (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u * (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹).val`. Introduce `u hu`. Simplify using `only [GlobalTheory.StepData.IntM, Filter.eventually_all]`. Introduce `i j`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases.

Use `filter_upwards [eventually_deep (u.val i j)] with m hm`. Rewrite using `[← map_inv, diag_mul_mul_diag]`. Establish `h1 : Deep (-((m : ℤ) * (i : ℕ)) + (m : ℤ) * (j : ℕ)) ((x ^ (-((m : ℤ) * (i : ℕ))) * (x ^ (-((m : ℤ) * (j : ℕ))))⁻¹ : kˣ) : k)`. Rewrite using `[← _root_.zpow_neg, neg_neg, ← _root_.zpow_add, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hx]`. Establish `h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ)` using `by exact_mod_cast Fin.lt_def.1 h`.

Conclude with `deep_zero_iff.1 ((h1.mul hm).mono (by nlinarith))`. Use `Filter.Eventually.of_forall fun m => ?_` and prove the remaining obligations. Rewrite using `[((mem_unipB k).1 (conj_mem_unipB _ hu)).2 i]`. Conclude with `one_mem _`. Use `Filter.Eventually.of_forall fun m => ?_` and prove the remaining obligations.

Rewrite using `[((mem_unipB k).1 (conj_mem_unipB _ hu)).1 i j h]`. Conclude with `zero_mem _`. Use `filter_upwards [key u hu, key _ (inv_mem hu)] with m h1 h2`. Use `⟨conj_mem_unipB _ hu, GlobalTheory.StepData.mem_KO.2 ⟨h1, ?_⟩⟩` and prove the remaining obligations. Use `h2 using 2` and compare the differences between its conclusion and the goal.

Use `group`.
-/
private theorem jqInj_ev {x : kˣ} (hx : valuation k (x : k) = uniformizer k) {u : GL (Fin n) k}
    (hu : u ∈ unipB k (Fin n)) : ∀ᶠ m : ℕ in Filter.atTop,
      diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹ ∈ unipO k n := by
  have key : ∀ u ∈ unipB k (Fin n), ∀ᶠ m : ℕ in Filter.atTop, GlobalTheory.StepData.IntM
      (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) * u *
        (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))))⁻¹).val := by
    intro u hu
    simp only [GlobalTheory.StepData.IntM, Filter.eventually_all]
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · filter_upwards [eventually_deep (u.val i j)] with m hm
      rw [← map_inv, diag_mul_mul_diag]
      have h1 : Deep (-((m : ℤ) * (i : ℕ)) + (m : ℤ) * (j : ℕ))
          ((x ^ (-((m : ℤ) * (i : ℕ))) * (x ^ (-((m : ℤ) * (j : ℕ))))⁻¹ : kˣ) : k) := by
        rw [← _root_.zpow_neg, neg_neg, ← _root_.zpow_add, Deep, Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
      have h2 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast Fin.lt_def.1 h
      exact deep_zero_iff.1 ((h1.mul hm).mono (by nlinarith))
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).2 i]
      exact one_mem _
    · refine Filter.Eventually.of_forall fun m => ?_
      rw [((mem_unipB k).1 (conj_mem_unipB _ hu)).1 i j h]
      exact zero_mem _
  filter_upwards [key u hu, key _ (inv_mem hu)] with m h1 h2
  refine ⟨conj_mem_unipB _ hu, GlobalTheory.StepData.mem_KO.2 ⟨h1, ?_⟩⟩
  convert h2 using 2
  group
/- English proof (translation)
Set `V` to `Sig.Lev.iw k`. Establish `hI : HeckePair (V.J n)` using `((Sig.finFacts k V).2.2.2.2.2 n).1`. Establish `hT : (Sig.dg d)⁻¹ ∈ (glIwa k n).Tf` using `inv_mem ⟨d, rfl⟩`. Establish `hfin : Finite (MulAction.orbit (V.J n) ((Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n))` using `(hI _).to_subtype`. Use `Finite.of_injective (fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N => (⟨(((q.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k), ⟨⟨q.out, V.N_le q.out.2⟩, rfl⟩⟩ : MulAction.orbit (V.J n) ((Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V. …` and prove the remaining obligations.

Introduce `q q' h`. Establish `h1 : ((((q.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n) = (((q'.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k)` using `congrArg Subtype.val h`. Establish `h2` using `QuotientGroup.eq.1 h1`. Use `set z : GL (Fin n) k := ((q.out : (glIwa k n).N) : GL (Fin n) k)⁻¹ * (q'.out : (glIwa k n).N) with hz`. Establish `hzN : z ∈ (glIwa k n).N` using `mul_mem (inv_mem q.out.2) q'.out.2`.

Establish `h3 : (Sig.dg d)⁻¹ * z * Sig.dg d ∈ V.J n`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hz]`. Use `group`. Establish `h4 : (Sig.dg d)⁻¹ * z * Sig.dg d ∈ (glIwa k n).N`.

Use `(glIwa k n).Tf_Nf _ hT z ((glIwa k n).N_le hzN)` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `⟨this, V.J_le_KO h3⟩`. Establish `h5 : z ∈ (glIwa k n).Nconj (Sig.dg d)` using `⟨_, h4, by`. Express the relevant statement in the definitionally equal form `Sig.dg d * ((Sig.dg d)⁻¹ * z * Sig.dg d) * (Sig.dg d)⁻¹ = z`.

Use the proof step `group⟩`. Establish `h6 : (QuotientGroup.mk q.out : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) = QuotientGroup.mk q'.out`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify `h5` using `[hz]`. Rewrite `h6` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis.
-/
private theorem quot_finite (d : Fin n → kˣ) :
    Finite ((glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) := by
  classical
  let V := Sig.Lev.iw k
  have hI : HeckePair (V.J n) := ((Sig.finFacts k V).2.2.2.2.2 n).1
  have hT : (Sig.dg d)⁻¹ ∈ (glIwa k n).Tf := inv_mem ⟨d, rfl⟩
  have hfin : Finite (MulAction.orbit (V.J n) ((Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n)) := (hI _).to_subtype
  refine Finite.of_injective
    (fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N =>
      (⟨(((q.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k), ⟨⟨q.out, V.N_le q.out.2⟩, rfl⟩⟩ :
        MulAction.orbit (V.J n) ((Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n))) ?_
  intro q q' h
  have h1 : ((((q.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n) =
      (((q'.out : (glIwa k n).N) : GL (Fin n) k) * Sig.dg d : GL (Fin n) k) := congrArg Subtype.val h
  have h2 := QuotientGroup.eq.1 h1
  set z : GL (Fin n) k := ((q.out : (glIwa k n).N) : GL (Fin n) k)⁻¹ * (q'.out : (glIwa k n).N) with hz
  have hzN : z ∈ (glIwa k n).N := mul_mem (inv_mem q.out.2) q'.out.2
  have h3 : (Sig.dg d)⁻¹ * z * Sig.dg d ∈ V.J n := by
    convert h2 using 1
    rw [hz]
    group
  have h4 : (Sig.dg d)⁻¹ * z * Sig.dg d ∈ (glIwa k n).N := by
    have := (glIwa k n).Tf_Nf _ hT z ((glIwa k n).N_le hzN)
    rw [inv_inv] at this
    exact ⟨this, V.J_le_KO h3⟩
  have h5 : z ∈ (glIwa k n).Nconj (Sig.dg d) :=
    ⟨_, h4, by
      change Sig.dg d * ((Sig.dg d)⁻¹ * z * Sig.dg d) * (Sig.dg d)⁻¹ = z
      group⟩
  have h6 : (QuotientGroup.mk q.out : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) =
      QuotientGroup.mk q'.out := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hz] using h5
  rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h6
/- English proof (translation)
Use `haveI := quot_finite d`. Use `letI : Fintype ((glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) := Fintype.ofFinite _`. Establish `hinj : Function.Injective fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N => ((q.out : (glIwa k n).N) : GL (Fin n) k)` using `fun q q' h => by`. Establish `h1 : q.out = q'.out` using `Subtype.ext h`. Establish `h2` using `congrArg (QuotientGroup.mk : (glIwa k n).N → (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) h1`.

Rewrite `h2` using `[QuotientGroup.out_eq', QuotientGroup.out_eq']`. Then use the resulting hypothesis. Use `⟨Finset.univ.image fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N => ((q.out : (glIwa k n).N) : GL (Fin n) k), fun u hu => ?_, fun M _ _ ρ v => ?_⟩` and prove the remaining obligations. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hu`. Conclude with `q.out.2`. Rewrite using `[Finset.sum_image (fun x _ y _ h => hinj h), Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply]`.
-/
private theorem reps (d : Fin n → kˣ) : ∃ s : Finset (GL (Fin n) k), (∀ u ∈ s, u ∈ (glIwa k n).N) ∧
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GL (Fin n) k) M) (v : M),
      (glIwa k n).uOp ρ (Sig.dg d) v = ∑ u ∈ s, ρ u (ρ (Sig.dg d) v) := by
  classical
  haveI := quot_finite d
  letI : Fintype ((glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) := Fintype.ofFinite _
  have hinj : Function.Injective fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N =>
      ((q.out : (glIwa k n).N) : GL (Fin n) k) := fun q q' h => by
    have h1 : q.out = q'.out := Subtype.ext h
    have h2 := congrArg (QuotientGroup.mk : (glIwa k n).N → (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N) h1
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h2
  refine ⟨Finset.univ.image fun q : (glIwa k n).N ⧸ ((glIwa k n).Nconj (Sig.dg d)).subgroupOf (glIwa k n).N =>
      ((q.out : (glIwa k n).N) : GL (Fin n) k), fun u hu => ?_, fun M _ _ ρ v => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hu
    exact q.out.2
  · rw [Finset.sum_image (fun x _ y _ h => hinj h), Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_mul, Module.End.mul_apply]
/- English proof (translation)
Set `ρ₀ : Representation ℂ (GL (Fin n) k) ℂ` to `Representation.trivial ℂ _ ℂ`. Establish `hq : IsUnit (resCard k : ℂ)` using `(Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit`. Take `⟨θ, hθ, -⟩` from `thetaEx k n ⊤ ℂ ℂ ρ₀ hq`. Set `w : fixd ρ₀ (iwC k n ⊤)` to `⟨1, fun _ _ => by simp [ρ₀]⟩`. Establish `h` using `jqTheta k n ⊤ ℂ ρ₀ θ hθ d w`.

Establish `hJ : (Sig.Lev.iw k).J n = iwC k n ⊤` using `(Sig.link k n).1`. Establish `hU` using `(Sig.hkMul k (Sig.Lev.iw k) n ℂ ρ₀).2 d hd`. Rewrite `hU` using `[hJ]`. Establish `hU' : (((θ d : Module.End ℂ (fixd ρ₀ (iwC k n ⊤))) w : ℂ)) = s.card`. Rewrite using `[hθ d hd]`.

Use `(hU w).trans ?_` and prove the remaining obligations. Rewrite using `[hs ℂ ρ₀]`. Simplify using `[ρ₀, w]`. Establish `hker : twKer ρ₀ (unipB k (Fin n)) 1 = ⊥`. Use `(Submodule.eq_bot_iff _).2 fun x hx => ?_` and prove the remaining obligations.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, v, rfl⟩` from `hy`. Simplify using `[ρ₀]`. Consider the case `zero => rfl`.

Consider the case `add a b _ _ ha hb => rw [ha, hb, add_zero]`. Consider the case `smul a y _ hy => rw [hy, smul_zero]`. Establish `e1 : ρ₀ (diagT k (Fin n) d) (w : ℂ) = w` using `by simp [ρ₀]`. Rewrite `h` using `[hU', UnramFixed.jacB_apply, jacBU_mk, e1, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, hker, Submodule.mem_bot, sub_eq_zero]`. Rewrite using `[h]`.

Simplify using `[w]`.
-/
private theorem idx {d : Fin n → kˣ} (hd : Dom d) {s : Finset (GL (Fin n) k)}
    (hs : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ (GL (Fin n) k) M) (v : M),
      (glIwa k n).uOp ρ (Sig.dg d) v = ∑ u ∈ s, ρ u (ρ (Sig.dg d) v)) :
    (s.card : ℂ) = (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) *
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) := by
  let ρ₀ : Representation ℂ (GL (Fin n) k) ℂ := Representation.trivial ℂ _ ℂ
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := thetaEx k n ⊤ ℂ ℂ ρ₀ hq
  let w : fixd ρ₀ (iwC k n ⊤) := ⟨1, fun _ _ => by simp [ρ₀]⟩
  have h := jqTheta k n ⊤ ℂ ρ₀ θ hθ d w
  have hJ : (Sig.Lev.iw k).J n = iwC k n ⊤ := (Sig.link k n).1
  have hU := (Sig.hkMul k (Sig.Lev.iw k) n ℂ ρ₀).2 d hd
  rw [hJ] at hU
  have hU' : (((θ d : Module.End ℂ (fixd ρ₀ (iwC k n ⊤))) w : ℂ)) = s.card := by
    rw [hθ d hd]
    refine (hU w).trans ?_
    rw [hs ℂ ρ₀]
    simp [ρ₀, w]
  have hker : twKer ρ₀ (unipB k (Fin n)) 1 = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, v, rfl⟩ := hy
      simp [ρ₀]
    | zero => rfl
    | add a b _ _ ha hb => rw [ha, hb, add_zero]
    | smul a y _ hy => rw [hy, smul_zero]
  have e1 : ρ₀ (diagT k (Fin n) d) (w : ℂ) = w := by simp [ρ₀]
  rw [hU', UnramFixed.jacB_apply, jacBU_mk, e1, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.eq, hker, Submodule.mem_bot, sub_eq_zero] at h
  rw [h]
  simp [w]
/- English proof (translation)
Establish `hD : Dom d` using `fun i j hij => by`. Break down `hij.eq_or_lt with rfl | h` into its components or cases. Conclude with `le_rfl`. Conclude with `(hd i j h).le`. Take `⟨s, hsN, hs⟩` from `reps (k := k) (n := n) d`.

Set `w : fixd τ (V.J n)` to `⟨v, hvJ⟩`. Establish `hI : HeckePair (V.J n)` using `((Sig.finFacts k V).2.2.2.2.2 n).1`. Establish `h1` using `(hkApply ℂ _ T τ _ _ (Sig.dg d) (hI (Sig.dg d))).1 w`. Establish `h2` using `(Sig.hkMul k V n T τ).2 d hD w`. Establish `h3 : ∑ u ∈ s, τ u (τ (Sig.dg d) v) = Dict.expo ψ d • v` using `(hs T τ v).symm.trans (h2.symm.trans (h1.trans h))`.

Establish `h4 : (Submodule.Quotient.mk (∑ u ∈ s, τ u (τ (Sig.dg d) v)) : Jacquet τ (unipB k (Fin n))) = (s.card : ℂ) • (Submodule.Quotient.mk (τ (Sig.dg d) v) : Jacquet τ (unipB k (Fin n)))`. Rewrite using `[← Submodule.mkQ_apply, map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun u hu => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.eq]`. Conclude with `sub_mem_twKer (π := τ) (hsN u hu).1 _`.

Establish `e` using `idx hD hs`. Rewrite `h4` using `[h3, e, Submodule.Quotient.mk_smul]`. Rewrite using `[UnramFixed.jacB_apply, jacBU_mk]`. Use `set c : ℂ := (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) with hc`. Establish `hc0 : c ≠ 0` using `Units.ne_zero _`.

Establish `hx : Dict.expo ψ d = (torusChar ψ d : ℂ) * c`. Rewrite using `[Dict.expo, Units.val_mul]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `c • (Submodule.Quotient.mk (τ (Sig.dg d) v) : Jacquet τ (unipB k (Fin n))) = _`. Rewrite `h4` using `[hx, mul_comm, mul_smul, mul_smul]`.

Conclude with `(smul_cancel hc0 h4).symm`.
-/
private theorem jac_eig {T : Type} [AddCommGroup T] [Module ℂ T] (V : Sig.Lev k) (ψ : Fin n → kˣ →* ℂˣ)
    (τ : Representation ℂ (GL (Fin n) k) T) {v : T} (hvJ : v ∈ fixd τ (V.J n)) {d : Fin n → kˣ} (hd : Sig.SDom d)
    (h : dc τ (V.J n) (V.J n) (Sig.dg d) v = Dict.expo ψ d • v) :
    jacB τ d (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) =
      (torusChar ψ d : ℂ) • (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) := by
  have hD : Dom d := fun i j hij => by
    rcases hij.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (hd i j h).le
  obtain ⟨s, hsN, hs⟩ := reps (k := k) (n := n) d
  let w : fixd τ (V.J n) := ⟨v, hvJ⟩
  have hI : HeckePair (V.J n) := ((Sig.finFacts k V).2.2.2.2.2 n).1
  have h1 := (hkApply ℂ _ T τ _ _ (Sig.dg d) (hI (Sig.dg d))).1 w
  have h2 := (Sig.hkMul k V n T τ).2 d hD w
  have h3 : ∑ u ∈ s, τ u (τ (Sig.dg d) v) = Dict.expo ψ d • v := (hs T τ v).symm.trans (h2.symm.trans (h1.trans h))
  have h4 : (Submodule.Quotient.mk (∑ u ∈ s, τ u (τ (Sig.dg d) v)) : Jacquet τ (unipB k (Fin n))) =
      (s.card : ℂ) • (Submodule.Quotient.mk (τ (Sig.dg d) v) : Jacquet τ (unipB k (Fin n))) := by
    rw [← Submodule.mkQ_apply, map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact sub_mem_twKer (π := τ) (hsN u hu).1 _
  have e := idx hD hs
  rw [h3, e, Submodule.Quotient.mk_smul] at h4
  rw [UnramFixed.jacB_apply, jacBU_mk]
  set c : ℂ := (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) d))⁻¹ : ℂˣ) : ℂ) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hx : Dict.expo ψ d = (torusChar ψ d : ℂ) * c := by
    rw [Dict.expo, Units.val_mul]
    rfl
  change c • (Submodule.Quotient.mk (τ (Sig.dg d) v) : Jacquet τ (unipB k (Fin n))) = _
  rw [hx, mul_comm, mul_smul, mul_smul] at h4
  exact (smul_cancel hc0 h4).symm
/- English proof (translation)
Introduce `hv`. Establish `h1 : v ∈ twKer τ (unipB k (Fin n)) 1` using `(Submodule.Quotient.mk_eq_zero _).1 hv`. Take `⟨c, hc⟩` from `valuation_surjective (uniformizer k)`. Establish `hc0 : c ≠ 0` using `fun h => by`. Rewrite `hc` using `[h, map_zero]`.

Conclude with `GlobalTheory.IwahoriInj.unif_pos.ne hc`. Establish `hx : valuation k ((Units.mk0 c hc0 : kˣ) : k) = uniformizer k` using `hc`. Generalize the expression as in `Units.mk0 c hc0 = x at hx`. Establish `hle : unipO k n ≤ V.J n` using `V.N_le`. Establish `h2 : ∀ w ∈ twKer τ (unipB k (Fin n)) 1, ∀ᶠ m : ℕ in Filter.atTop, τ (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w ∈ twKer τ (V.J n) 1`.

Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, w, rfl⟩` from `hy`. Use `filter_upwards [jqInj_ev hx u.2] with m hm`.

Use `GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hle hm) (τ (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w)` as an intermediate fact. Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, ← map_sub]`. Simplify `this` using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => filter_upwards [ha, hb] with m h1 h2`.

Rewrite using `[map_add]`. Conclude with `add_mem h1 h2`. Consider the case `smul a y _ hy => filter_upwards [hy] with m h1`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ a h1`.

Take `⟨m, hm, hm1⟩` from `((h2 _ h1).and (Filter.eventually_gt_atTop 0)).exists`. Establish `hd` using `jqInj_dom (n := n) hx m`. Establish `hsd : Sig.SDom (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))`. Introduce `i j hij`. Simplify using `only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]`.

Use `(zpow_lt_zpow_iff_right_of_lt_one₀ unif_pos uniformizer_lt_one).2 ?_` and prove the remaining obligations. Establish `h3 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ)` using `by exact_mod_cast Fin.lt_def.1 hij`. Establish `h4 : (1 : ℤ) ≤ m` using `by exact_mod_cast hm1`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨s, hsN, hs⟩` from `reps (k := k) (n := n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))`.

Set `w : fixd τ (V.J n)` to `⟨v, hvJ⟩`. Establish `hF` using `(Sig.finFacts k V).2.2.2.2.2 n`. Establish `h3` using `(hkApply ℂ _ T τ _ _ (Sig.dg fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) (hF.1 _)).1 w`. Establish `h4` using `(Sig.hkMul k V n T τ).2 _ hd w`. Establish `h5 : (hk τ (V.J n) (Sig.dg fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) w : T) = 0`.

Use `GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hF.2.2.1 (GlobalTheory.IwahoriInj.mem_fixed.2 (hk τ (V.J n) _ w).2) ?_` and prove the remaining obligations. Rewrite using `[h4, hs T τ]`. Use `Submodule.sum_mem _ fun u hu => ?_` and prove the remaining obligations. Conclude with `GlobalTheory.IwahoriInj.apply_mem_twKer (V.N_le (hsN u hu)) hm`. Establish `h6 : e _ • v = 0` using `((hE _ hsd).symm.trans h3.symm).trans h5`.

Conclude with `hv0 ((smul_eq_zero.1 h6).resolve_left (he _))`.
-/
private theorem mk_ne {T : Type} [AddCommGroup T] [Module ℂ T] (V : Sig.Lev k) (τ : Representation ℂ (GL (Fin n) k) T)
    (hτ : IsSmooth τ) {v : T} (hv0 : v ≠ 0) (hvJ : v ∈ fixd τ (V.J n)) (e : (Fin n → kˣ) → ℂ) (he : ∀ d, e d ≠ 0)
    (hE : ∀ d, Sig.SDom d → dc τ (V.J n) (V.J n) (Sig.dg d) v = e d • v) :
    (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) ≠ 0 := by
  intro hv
  have h1 : v ∈ twKer τ (unipB k (Fin n)) 1 := (Submodule.Quotient.mk_eq_zero _).1 hv
  obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
  have hc0 : c ≠ 0 := fun h => by
    rw [h, map_zero] at hc
    exact GlobalTheory.IwahoriInj.unif_pos.ne hc
  have hx : valuation k ((Units.mk0 c hc0 : kˣ) : k) = uniformizer k := hc
  generalize Units.mk0 c hc0 = x at hx
  have hle : unipO k n ≤ V.J n := V.N_le
  have h2 : ∀ w ∈ twKer τ (unipB k (Fin n)) 1, ∀ᶠ m : ℕ in Filter.atTop,
      τ (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w ∈ twKer τ (V.J n) 1 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, w, rfl⟩ := hy
      filter_upwards [jqInj_ev hx u.2] with m hm
      have := GlobalTheory.IwahoriInj.sub_mem_twKer (π := τ) (hle hm)
        (τ (diagT k (Fin n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))) w)
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply, ← map_sub] at this
      simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using this
    | zero => simp
    | add a b _ _ ha hb =>
      filter_upwards [ha, hb] with m h1 h2
      rw [map_add]
      exact add_mem h1 h2
    | smul a y _ hy =>
      filter_upwards [hy] with m h1
      rw [map_smul]
      exact Submodule.smul_mem _ a h1
  obtain ⟨m, hm, hm1⟩ := ((h2 _ h1).and (Filter.eventually_gt_atTop 0)).exists
  have hd := jqInj_dom (n := n) hx m
  have hsd : Sig.SDom (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) := by
    intro i j hij
    simp only [Units.val_zpow_eq_zpow_val, map_zpow₀, hx]
    refine (zpow_lt_zpow_iff_right_of_lt_one₀ unif_pos uniformizer_lt_one).2 ?_
    have h3 : ((i : ℕ) : ℤ) + 1 ≤ (j : ℕ) := by exact_mod_cast Fin.lt_def.1 hij
    have h4 : (1 : ℤ) ≤ m := by exact_mod_cast hm1
    nlinarith
  obtain ⟨s, hsN, hs⟩ := reps (k := k) (n := n) (fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ))))
  let w : fixd τ (V.J n) := ⟨v, hvJ⟩
  have hF := (Sig.finFacts k V).2.2.2.2.2 n
  have h3 := (hkApply ℂ _ T τ _ _ (Sig.dg fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) (hF.1 _)).1 w
  have h4 := (Sig.hkMul k V n T τ).2 _ hd w
  have h5 : (hk τ (V.J n) (Sig.dg fun i : Fin n => x ^ (-((m : ℤ) * (i : ℕ)))) w : T) = 0 := by
    refine GlobalTheory.IwahoriInj.eq_zero_of_fixed hτ hF.2.2.1 (GlobalTheory.IwahoriInj.mem_fixed.2 (hk τ (V.J n) _ w).2) ?_
    rw [h4, hs T τ]
    refine Submodule.sum_mem _ fun u hu => ?_
    exact GlobalTheory.IwahoriInj.apply_mem_twKer (V.N_le (hsN u hu)) hm
  have h6 : e _ • v = 0 := ((hE _ hsd).symm.trans h3.symm).trans h5
  exact hv0 ((smul_eq_zero.1 h6).resolve_left (he _))
end Lev
/- English proof (translation)
Introduce `H k _ _ _ _ n V ψ hψ T _ _ τ hs hi v hv0 hvJ heig`. Establish `hx : (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) ≠ 0` using `mk_ne V τ hs hv0 hvJ (Dict.expo ψ) (fun d => Units.ne_zero _) heig`. Establish `hsd` using `fun d (hd : Sig.SDom d) => jac_eig V ψ τ hvJ hd (heig d hd)`. Establish `ht : ∀ t, jacB τ t (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) = (torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n)))`. Introduce `t`.

Take `⟨d, hd, htd⟩` from `exists_sdom t`. Establish `h1` using `hsd d hd`. Establish `h2` using `hsd (t * d) htd`. Rewrite `h2` using `[map_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul]`. Conclude with `smul_cancel (Units.ne_zero (torusChar ψ d)) h2`.

Establish `hl : HasFiniteLength (jacB τ)` using `(hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2 ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ τ hs (hasFiniteLength_of_isIrreducible hi))`. Use `haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k`. Take `⟨-, l, hl0, hle⟩` from `exists_form (χ := torusChar ψ) (isSmooth_jacB hs) hl hx fun t => ⟨1, by rw [pow_one, LinearMap.sub_apply, Module.algebraMap_end_apply, ht t, sub_self]⟩`. Conclude with `GlobalTheory.SatakeExists.isSubquotient_of_eigenform hs hi (torusChar ψ) l hl0 hle`.
-/
theorem UpperTheory.V.Z.Sym.W.local_sub_d_statement :
    _root_.UpperTheory.V.Z.Sym.W.LocSubDAlt := by
  intro H k _ _ _ _ n V ψ hψ T _ _ τ hs hi v hv0 hvJ heig
  have hx : (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) ≠ 0 :=
    mk_ne V τ hs hv0 hvJ (Dict.expo ψ) (fun d => Units.ne_zero _) heig
  have hsd := fun d (hd : Sig.SDom d) => jac_eig V ψ τ hvJ hd (heig d hd)
  have ht : ∀ t, jacB τ t (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) =
      (torusChar ψ t : ℂ) • (Submodule.Quotient.mk v : Jacquet τ (unipB k (Fin n))) := by
    intro t
    obtain ⟨d, hd, htd⟩ := exists_sdom t
    have h1 := hsd d hd
    have h2 := hsd (t * d) htd
    rw [map_mul, Module.End.mul_apply, h1, map_smul, map_mul, Units.val_mul, mul_comm, mul_smul] at h2
    exact smul_cancel (Units.ne_zero (torusChar ψ d)) h2
  have hl : HasFiniteLength (jacB τ) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ τ hs (hasFiniteLength_of_isIrreducible hi))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨-, l, hl0, hle⟩ := exists_form (χ := torusChar ψ) (isSmooth_jacB hs) hl hx fun t =>
    ⟨1, by rw [pow_one, LinearMap.sub_apply, Module.algebraMap_end_apply, ht t, sub_self]⟩
  exact GlobalTheory.SatakeExists.isSubquotient_of_eigenform hs hi (torusChar ψ) l hl0 hle
end
