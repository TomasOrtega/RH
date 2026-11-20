import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalDenominators
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsBasisLocF
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section

open scoped Classical
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.LocalDenominators

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Rewrite using `[D.conjF_eq, D.conjF_eq]`. Conclude with `D.embE.injective (by rw [D.embE_conj, D.embE_conj, star_star])`.
-/
theorem conjF_invol (e : D.host.E) : D.conjF (D.conjF e) = e := by
  rw [D.conjF_eq, D.conjF_eq]
  exact D.embE.injective (by rw [D.embE_conj, D.embE_conj, star_star])

/- English proof (translation)
Rewrite `h` using `[D.conjF_eq]`. Establish `hy` using `(Formalism.BasicNotions.Examples₂.conj_eq_self_iff D.host y).1 h`. Conclude with `⟨⟨y, hy⟩, rfl⟩`.
-/
theorem conjF_fix (y : D.host.E) (h : D.conjF y = y) : y ∈ (algebraMap D.host.F D.host.E).range := by
  rw [D.conjF_eq] at h
  have hy := (Formalism.BasicNotions.Examples₂.conj_eq_self_iff D.host y).1 h
  exact ⟨⟨y, hy⟩, rfl⟩

/- English proof (translation)
The claim follows from `iE_mem_O_iff (D.s.atP p) conjF_invol conjF_fix x`.
-/
theorem iE_mem_O_iff_D (p : PlF D) (x : D.host.E) :
    (D.s.atP p).ιE x ∈ (D.s.atP p).O ↔
      ∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * x) :=
  iE_mem_O_iff (D.s.atP p) conjF_invol conjF_fix x

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `show (D.s.atP p).ιE ((VS D).frame.repr (c • x) i) = (D.s.atP p).ιE c * (D.s.atP p).ιE ((VS D).frame.repr x i)`. Rewrite using `[LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]`.
-/
theorem baseChange_smul₂ (p : PlF D) (c : D.host.E) (x : (VS D).V) :
    baseChange₂ D p (c • x : (VS D).V) = ((D.s.atP p).ιE c • (baseChange₂ D p x : Vp D p) : Vp D p) := by
  funext i
  show (D.s.atP p).ιE ((VS D).frame.repr (c • x) i) =
    (D.s.atP p).ιE c * (D.s.atP p).ιE ((VS D).frame.repr x i)
  rw [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]

def chat (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (v : Vp D p) : (D.s.atP p).Ep :=
  ∑ j, (D.s.atP p).ιE (w ((VS D).frame j)) * v j

/- English proof (translation)
Unfold `chat`. Use `conv_rhs => rw [← (VS D).frame.sum_repr y]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smul, smul_eq_mul, map_mul, mul_comm]`.

Both sides reduce to the same expression.
-/
theorem chat_bcP (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (y : (VS D).V) :
    chat p w (baseChange₂ D p y) = (D.s.atP p).ιE (w y) := by
  unfold chat
  conv_rhs => rw [← (VS D).frame.sum_repr y]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, map_mul, mul_comm]
  rfl

/- English proof (translation)
Simplify using `only [chat, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem chat_add (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (v v' : Vp D p) :
    chat p w (v + v') = chat p w v + chat p w v' := by
  simp only [chat, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [chat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem chat_smul (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) (a : (D.s.atP p).Ep) (v : Vp D p) :
    chat p w (a • v) = a * chat p w v := by
  simp only [chat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Simplify using `[chat]`.
-/
theorem chat_zero (p : PlF D) (w : (VS D).V →ₗ[D.host.E] D.host.E) : chat p w 0 = 0 := by
  simp [chat]

/- English proof (translation)
Apply `alg_mem_O` to reduce the goal to its premises. Rewrite using `[Valuation.mem_integer_iff, map_inv₀, iF_unit _ ht, inv_one]`.
-/
theorem iE_t_inv_mem (p : PlF D) {t : 𝓞 D.host.F} (ht : t ∉ p.asIdeal) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ ∈ (D.s.atP p).O := by
  apply alg_mem_O
  rw [Valuation.mem_integer_iff, map_inv₀, iF_unit _ ht, inv_one]

/- English proof (translation)
Establish `h0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `ht p.asIdeal.zero_mem`. Conclude with `(map_ne_zero _).mpr (by simpa using h0)`.
-/
theorem iF_t_ne (p : PlF D) {t : 𝓞 D.host.F} (ht : t ∉ p.asIdeal) : (D.s.atP p).ιF (t : D.host.F) ≠ 0 := by
  have h0 : t ≠ 0 := by
    rintro rfl
    exact ht p.asIdeal.zero_mem
  exact (map_ne_zero _).mpr (by simpa using h0)

section Dict

variable (Zd : LocDat D) (p : PlF D)

instance finVS : FiniteDimensional D.host.E (VS D).V := Module.Finite.of_basis (VS D).frame

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `exact (algebraMap_smul D.host.E c x).symm`.
-/
theorem oE_smul (c : 𝓞 D.host.E) (x : (VS D).V) : c • x = ((c : D.host.E)) • x := by
  first
  | rfl
  | exact (algebraMap_smul D.host.E c x).symm

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp`. Consider the case `exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E t).symm`.
-/
theorem oF_coe (t : 𝓞 D.host.F) :
    ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t : 𝓞 D.host.E) : D.host.E) = algebraMap D.host.F D.host.E (t : D.host.F) := by
  first
  | rfl
  | simp
  | exact (IsScalarTower.algebraMap_apply (𝓞 D.host.F) D.host.F D.host.E t).symm

/- English proof (translation)
Conclude with `(Zd.agree p).2.2.2.1`.
-/
theorem hO : (Zd.M p).L.O = (D.s.atP p).O := by
  exact (Zd.agree p).2.2.2.1

/- English proof (translation)
Establish `ha' : a ∈ (Zd.M p).L.O`. Rewrite using `[hO]`. Conclude with `ha`. Conclude with `(lattice₂ D Zd.M p Λ).smul_mem ⟨a, ha'⟩ hv`.
-/
theorem smul_mem_localLattice {Λ : Submodule (𝓞 D.host.E) (VS D).V} {a : (D.s.atP p).Ep} (ha : a ∈ (D.s.atP p).O)
    {v : Vp D p} (hv : v ∈ lattice₂ D Zd.M p Λ) : a • v ∈ lattice₂ D Zd.M p Λ := by
  have ha' : a ∈ (Zd.M p).L.O := by
    rw [hO]
    exact ha
  exact (lattice₂ D Zd.M p Λ).smul_mem ⟨a, ha'⟩ hv

/- English proof (translation)
Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Rewrite using `[Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`.

Conclude with `isIntegral_one`. Conclude with `isIntegral_zero`. Consider the case `zero => simp [isIntegral_zero]`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `hx.add hy`. Consider the case `smul c y _ hy`. Rewrite using `[oE_smul, map_smul, smul_eq_mul]`. Conclude with `(RingOfIntegers.isIntegral_coe c).mul hy`.
-/
theorem coord_int {b : Module.Basis (Fin (Module.finrank D.host.E (VS D).V)) D.host.E (VS D).V} (i : Fin _)
    {z : (VS D).V} (hz : z ∈ Submodule.span (𝓞 D.host.E) (Set.range b)) : IsIntegral ℤ (b.coord i z) := by
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  | zero => simp [isIntegral_zero]
  | add x y _ _ hx hy =>
    rw [map_add]
    exact hx.add hy
  | smul c y _ hy =>
    rw [oE_smul, map_smul, smul_eq_mul]
    exact (RingOfIntegers.isIntegral_coe c).mul hy

/- English proof (translation)
Use `haveI := p.isPrime`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨b, hbΛ, hbloc⟩` from `Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hΛ p.isMaximal`. Establish `key : ∀ i, (D.s.atP p).ιE (b.coord i x) ∈ (D.s.atP p).O`.

Introduce `i`. Establish `hcall : ∀ v ∈ lattice₂ D Zd.M p Λ, chat p (b.coord i) v ∈ (D.s.atP p).O`. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`.

Take `⟨y, hy, rfl⟩` from `hv`. Rewrite using `[chat_bcP]`. Establish `hy' : y ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range b))`. Rewrite using `[hbloc]; exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ y).2 ⟨1, fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hy⟩`. Take `⟨t, ht, hty⟩` from `(Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal _ y).1 hy'`.

Establish `hint` using `coord_int i hty`. Rewrite `hint` using `[oE_smul, oF_coe, map_smul, smul_eq_mul]`. Establish `h1` using `iE_int (D.s.atP p) hint`. Rewrite `h1` using `[map_mul, iE_alg]`. Establish `e : (D.s.atP p).ιE (b.coord i y) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) * (D.s.atP p).ιE (b.coord i y))`.

Rewrite using `[← mul_assoc, ← map_mul, inv_mul_cancel₀ (iF_t_ne p ht), map_one, one_mul]`. Rewrite using `[e]`. Conclude with `(D.s.atP p).O.mul_mem (iE_t_inv_mem p ht) h1`. Consider the case `zero => rw [chat_zero]`. Conclude with `(D.s.atP p).O.zero_mem`.

Consider the case `add a c _ _ ha hc => rw [chat_add]`. Conclude with `(D.s.atP p).O.add_mem ha hc`. Consider the case `smul a v _ hv`. Establish `ha : (a : (D.s.atP p).Ep) ∈ (D.s.atP p).O` using `by rw [← hO Zd p]; exact a.2`. Establish `e : a • v = (a : (D.s.atP p).Ep) • v` using `rfl`.

Rewrite using `[e, chat_smul]`. Conclude with `(D.s.atP p).O.mul_mem ha hv`. Establish `hc` using `hcall _ hx`. Rewrite `hc` using `[chat_bcP]`. Then use the resulting hypothesis. Establish `hint : ∀ i, ∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧ IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * b.coord i x)` using `fun i => (iE_mem_O_iff_D p _).1 (key i)`.

Use `choose s hs hsi using hint`. Use `set t : 𝓞 D.host.F := ∏ i, s i with htdef`. Establish `ht : t ∉ p.asIdeal`. Rewrite using `[htdef]`. Introduce `h`.

Take `⟨i, -, hi⟩` from `Ideal.IsPrime.prod_mem_iff.1 h`. Conclude with `hs i hi`. Establish `hsF : ∀ j, IsIntegral ℤ (algebraMap D.host.F D.host.E (s j : D.host.F))` using `fun j => by`. Use `(s j).2` as an intermediate fact. Conclude with `(show IsIntegral ℤ ((s j : D.host.F)) from (s j).2).map (algebraMap D.host.F D.host.E).toIntAlgHom`.

Establish `hT : ∀ i, IsIntegral ℤ (algebraMap D.host.F D.host.E (t : D.host.F) * b.coord i x)`. Introduce `i`. Establish `e : algebraMap D.host.F D.host.E (t : D.host.F) = (∏ j ∈ Finset.univ.erase i, algebraMap D.host.F D.host.E (s j : D.host.F)) * algebraMap D.host.F D.host.E (s i : D.host.F)` using `by show algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) = _`. Rewrite using `[htdef, map_prod, map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]`. Rewrite using `[e, mul_assoc]`.

Use `IsIntegral.mul ?_ (hsi i)` and prove the remaining obligations. Conclude with `Finset.prod_induction _ (fun z => IsIntegral ℤ z) (fun a c ha hc => ha.mul hc) isIntegral_one (fun j _ => hsF j)`. Establish `hx' : x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range b))`. Use `(Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal _ x).2 ⟨t, ht, ?_⟩` and prove the remaining obligations. Rewrite using `[oE_smul, oF_coe]`.

Establish `ex : x = ∑ i, b.repr x i • b i` using `(b.sum_repr x).symm`. Rewrite using `[ex, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Establish `hTi : IsIntegral ℤ (algebraMap D.host.F D.host.E (t : D.host.F) * b.repr x i)` using `hT i`.

Establish `hmem` using `Submodule.smul_mem (Submodule.span (𝓞 D.host.E) (Set.range b)) (⟨_, hTi⟩ : 𝓞 D.host.E) (Submodule.subset_span ⟨i, rfl⟩ : b i ∈ Submodule.span (𝓞 D.host.E) (Set.range b))`. Use `hmem using 1` and compare the differences between its conclusion and the goal. Conclude with `(oE_smul (⟨_, hTi⟩ : 𝓞 D.host.E) (b i)).symm`. Rewrite `hx'` using `[hbloc]`. Then use the resulting hypothesis. Introduce `hx`.

Take `⟨t, ht, htx⟩` from `(Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).1 hx`. Establish `h1 : baseChange₂ D p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x) ∈ lattice₂ D Zd.M p Λ` using `Submodule.subset_span ⟨_, htx, rfl⟩`. Rewrite `h1` using `[oE_smul, oF_coe, baseChange_smul₂, iE_alg]`. Establish `e : baseChange₂ D p x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) • baseChange₂ D p x)`. Rewrite using `[smul_smul, ← map_mul, inv_mul_cancel₀ (iF_t_ne p ht), map_one, one_smul]`.

Rewrite using `[e]`. Conclude with `smul_mem_localLattice Zd p (iE_t_inv_mem p ht) h1`.
-/
theorem baseChangeAt_mem_localLattice_iff {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsLattice D.host.E Λ) (x : (VS D).V) :
    baseChange₂ D p x ∈ lattice₂ D Zd.M p Λ ↔ x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal Λ := by
  haveI := p.isPrime
  constructor
  · intro hx
    obtain ⟨b, hbΛ, hbloc⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hΛ p.isMaximal
    have key : ∀ i, (D.s.atP p).ιE (b.coord i x) ∈ (D.s.atP p).O := by
      intro i
      have hcall : ∀ v ∈ lattice₂ D Zd.M p Λ, chat p (b.coord i) v ∈ (D.s.atP p).O := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨y, hy, rfl⟩ := hv
          rw [chat_bcP]
          have hy' : y ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
            rw [hbloc]; exact (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ y).2 ⟨1, fun h => p.isPrime.ne_top
              ((Ideal.eq_top_iff_one _).2 h), by simpa using hy⟩
          obtain ⟨t, ht, hty⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal _ y).1 hy'
          have hint := coord_int i hty
          rw [oE_smul, oF_coe, map_smul, smul_eq_mul] at hint
          have h1 := iE_int (D.s.atP p) hint
          rw [map_mul, iE_alg] at h1
          have e : (D.s.atP p).ιE (b.coord i y) =
              algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ *
              (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) * (D.s.atP p).ιE (b.coord i y)) := by
            rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (iF_t_ne p ht), map_one, one_mul]
          rw [e]
          exact (D.s.atP p).O.mul_mem (iE_t_inv_mem p ht) h1
        | zero => rw [chat_zero]; exact (D.s.atP p).O.zero_mem
        | add a c _ _ ha hc => rw [chat_add]; exact (D.s.atP p).O.add_mem ha hc
        | smul a v _ hv =>
          have ha : (a : (D.s.atP p).Ep) ∈ (D.s.atP p).O := by rw [← hO Zd p]; exact a.2
          have e : a • v = (a : (D.s.atP p).Ep) • v := rfl
          rw [e, chat_smul]
          exact (D.s.atP p).O.mul_mem ha hv
      have hc := hcall _ hx
      rwa [chat_bcP] at hc
    have hint : ∀ i, ∃ s : 𝓞 D.host.F, s ∉ p.asIdeal ∧
        IsIntegral ℤ (algebraMap D.host.F D.host.E (s : D.host.F) * b.coord i x) := fun i =>
      (iE_mem_O_iff_D p _).1 (key i)
    choose s hs hsi using hint
    set t : 𝓞 D.host.F := ∏ i, s i with htdef
    have ht : t ∉ p.asIdeal := by
      rw [htdef]
      intro h
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 h
      exact hs i hi
    have hsF : ∀ j, IsIntegral ℤ (algebraMap D.host.F D.host.E (s j : D.host.F)) := fun j => by
      have := (s j).2
      exact (show IsIntegral ℤ ((s j : D.host.F)) from (s j).2).map (algebraMap D.host.F D.host.E).toIntAlgHom
    have hT : ∀ i, IsIntegral ℤ (algebraMap D.host.F D.host.E (t : D.host.F) * b.coord i x) := by
      intro i
      have e : algebraMap D.host.F D.host.E (t : D.host.F) =
          (∏ j ∈ Finset.univ.erase i, algebraMap D.host.F D.host.E (s j : D.host.F)) *
            algebraMap D.host.F D.host.E (s i : D.host.F) := by
        show algebraMap D.host.F D.host.E (algebraMap (𝓞 D.host.F) D.host.F t) = _
        rw [htdef, map_prod, map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      rw [e, mul_assoc]
      refine IsIntegral.mul ?_ (hsi i)
      exact Finset.prod_induction _ (fun z => IsIntegral ℤ z) (fun a c ha hc => ha.mul hc) isIntegral_one
        (fun j _ => hsF j)
    have hx' : x ∈ Formalism.HermitianLattices.Ext.L3.locF p.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range b)) := by
      refine (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal _ x).2 ⟨t, ht, ?_⟩
      rw [oE_smul, oF_coe]
      have ex : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
      rw [ex, Finset.smul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [smul_smul]
      have hTi : IsIntegral ℤ (algebraMap D.host.F D.host.E (t : D.host.F) * b.repr x i) := hT i
      have hmem := Submodule.smul_mem (Submodule.span (𝓞 D.host.E) (Set.range b)) (⟨_, hTi⟩ : 𝓞 D.host.E)
        (Submodule.subset_span ⟨i, rfl⟩ : b i ∈ Submodule.span (𝓞 D.host.E) (Set.range b))
      convert hmem using 1
      exact (oE_smul (⟨_, hTi⟩ : 𝓞 D.host.E) (b i)).symm
    rwa [hbloc] at hx'
  · intro hx
    obtain ⟨t, ht, htx⟩ := (Formalism.HermitianLattices.Ext.L3.LocalSpans.mem_locF p.asIdeal Λ x).1 hx
    have h1 : baseChange₂ D p (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t • x) ∈ lattice₂ D Zd.M p Λ :=
      Submodule.subset_span ⟨_, htx, rfl⟩
    rw [oE_smul, oF_coe, baseChange_smul₂, iE_alg] at h1
    have e : baseChange₂ D p x = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F))⁻¹ •
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF (t : D.host.F)) • baseChange₂ D p x) := by
      rw [smul_smul, ← map_mul, inv_mul_cancel₀ (iF_t_ne p ht), map_one, one_smul]
    rw [e]
    exact smul_mem_localLattice Zd p (iE_t_inv_mem p ht) h1

end Dict

end Formalism.L2.SG.Pf.LocalDenominators
