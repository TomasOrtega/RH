import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.WBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HGZeroRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.PrincipalIdealRingAtPrime

noncomputable section

open NumberField Formalism.MainNotions.S
open PI.ScRefExists.Sk

namespace PI.ScRefExists.WB

variable (I : Formalism.MainNotions.S.AutInst)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem smul_Ap {p : ℕ} (c : Ap I p) (x : Fin I.n → I.E) : c • x = (c : I.E) • x := rfl

def WA (p r : ℕ) (e f : Fin r → Fin I.n → I.E) : Submodule (Ap I p) (Fin I.n → I.E) :=
  LA I p ⊓
  { carrier := {x | ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0}
    add_mem' := by
      intro x y hx hy
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      intro a
      exact ⟨by rw [hG_add_right, (hx a).1, (hy a).1, add_zero],
        by rw [hG_add_right, (hx a).2, (hy a).2, add_zero]⟩
    zero_mem' := by
      simp only [Set.mem_setOf_eq]
      intro a
      exact ⟨hG_zero_right I _, hG_zero_right I _⟩
    smul_mem' := by
      intro c x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      intro a
      exact ⟨by rw [smul_Ap, hG_smul_right, (hx a).1, mul_zero],
        by rw [smul_Ap, hG_smul_right, (hx a).2, mul_zero]⟩ }

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_WA {p r : ℕ} {e f : Fin r → Fin I.n → I.E} {x : Fin I.n → I.E} :
    x ∈ WA I p r e f ↔ x ∈ LA I p ∧ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0 := Iff.rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `I.L_fg`. Use `⟨s, ?_⟩` and prove the remaining obligations. Unfold `LA`. Rewrite using `[← hs, Submodule.span_span_of_tower]`.
-/
theorem LA_fg (p : ℕ) : (LA I p).FG := by
  obtain ⟨s, hs⟩ := I.L_fg
  refine ⟨s, ?_⟩
  unfold LA
  rw [← hs, Submodule.span_span_of_tower]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span hy`. Consider the case `zero => exact zero_mem _`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `smul c y _ hy => rw [smul_Ap]`.

Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem span_Ap_le {p : ℕ} (s : Set (Fin I.n → I.E)) {x : Fin I.n → I.E}
    (hx : x ∈ Submodule.span (Ap I p) s) : x ∈ Submodule.span I.E s := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy => rw [smul_Ap]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Establish `hle : WA I p r e f ≤ LA I p` using `fun x hx => (mem_WA I).mp hx |>.1`. Use `haveI : IsNoetherian (Ap I p) (LA I p) := isNoetherian_of_fg_of_noetherian _ (LA_fg I p)`. Establish `hfg : ((WA I p r e f).comap (LA I p).subtype).FG` using `IsNoetherian.noetherian _`. Establish `hmap : ((WA I p r e f).comap (LA I p).subtype).map (LA I p).subtype = WA I p r e f`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.mpr hle]`.

Rewrite using `[Module.Finite.iff_fg, ← hmap]`. Conclude with `hfg.map _`.
-/
theorem WA_finite {p r : ℕ} (e f : Fin r → Fin I.n → I.E) [IsPrincipalIdealRing (Ap I p)] :
    Module.Finite (Ap I p) (WA I p r e f) := by
  have hle : WA I p r e f ≤ LA I p := fun x hx => (mem_WA I).mp hx |>.1
  haveI : IsNoetherian (Ap I p) (LA I p) := isNoetherian_of_fg_of_noetherian _ (LA_fg I p)
  have hfg : ((WA I p r e f).comap (LA I p).subtype).FG := IsNoetherian.noetherian _
  have hmap : ((WA I p r e f).comap (LA I p).subtype).map (LA I p).subtype = WA I p r e f := by
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle]
  rw [Module.Finite.iff_fg, ← hmap]
  exact hfg.map _

/- English proof (translation)
Introduce `I p r k e f M hp hPID hn hee hff hef hM hMe`. Use `haveI := hPID`. Establish `hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0`. Introduce `a b`. Rewrite using `[hG_symm, hef]`.

Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (Ne.symm h), star_zero]`. Set `φ : (Fin I.n → I.E) →ₗ[I.E] (Fin r → I.E) × (Fin r → I.E)` to `{ toFun := fun x => (fun a => hG I (e a) x, fun a => hG I (f a) x) map_add' := fun x y => by`.

Apply the tactic sequence `refine Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;> simp [hG_add_right]`. Use the proof step `map_smul' := fun c x => by`. Apply the tactic sequence `refine Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;> simp [hG_smul_right] }`. Establish `hφ : ∀ x, x ∈ LinearMap.ker φ ↔ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0`. Introduce `x`.

Simplify using `only [LinearMap.mem_ker, φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.ext_iff, funext_iff, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]`. Conclude with `⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩`. Establish `hsurj : Function.Surjective φ`. Introduce and unpack `⟨s, t⟩`. Use `⟨∑ b, (s b • f b + t b • e b), ?_⟩` and prove the remaining obligations.

Use `Prod.ext (funext fun a => ?_) (funext fun a => ?_)` and prove the remaining obligations. Simplify using `[φ, hG_sum_right, hG_add_right, hG_smul_right, hef, hee, Prod.fst_sum, Finset.sum_apply]`. Simplify using `[φ, hG_sum_right, hG_add_right, hG_smul_right, hfe, hff, Prod.snd_sum, Finset.sum_apply]`. Establish `hker : Module.finrank I.E (LinearMap.ker φ) = k + 1`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker φ`.

Rewrite `h1` using `[LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]`. Use linear arithmetic over natural numbers and integers. Establish `hNZ : NoZeroSMulDivisors (Ap I p) (WA I p r e f)`. Use `⟨fun {c x} h => ?_⟩` and prove the remaining obligations. Establish `h2 : (c : I.E) • (x : Fin I.n → I.E) = 0`.

Use `congrArg Subtype.val h` as an intermediate fact. Simplify `this` using `[smul_Ap]`. Break down `smul_eq_zero.1 h2 with h3 | h3` into its components or cases. Use `left`. Conclude with `Subtype.ext h3`.

Use `right`. Conclude with `Subtype.ext h3`. Use `haveI := hNZ`. Use `haveI := WA_finite I (p := p) e f`. Use `haveI : Module.Free (Ap I p) (WA I p r e f) := Module.free_of_finite_type_torsion_free'`.

Establish `hLI : ∀ {ι : Type} [Fintype ι] (bb : Module.Basis ι (Ap I p) (WA I p r e f)), LinearIndependent I.E (fun j => ((bb j : WA I p r e f) : Fin I.n → I.E))`. Introduce `ι _ bb`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg j`. Take `⟨dd, hdd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 I.E)) Finset.univ g`.

Use `choose a ha using fun i => hdd i (Finset.mem_univ i)`. Establish `hsum : ∑ i, (⟨algebraMap (𝓞 I.E) I.E (a i), (Ap I p).algebraMap_mem (a i)⟩ : Ap I p) • bb i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, smul_Ap, ZeroMemClass.coe_zero]`. Establish `: ∑ i, ((dd : 𝓞 I.E) : I.E) • (g i • ((bb i : WA I p r e f) : Fin I.n → I.E)) = 0`.

Rewrite using `[← Finset.smul_sum, hg, smul_zero]`. Rewrite using `[← this]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ha i, Algebra.smul_def]`. Both sides reduce to the same expression.

Establish `hz` using `(Fintype.linearIndependent_iff.1 bb.linearIndependent) _ hsum j`. Establish `h0 : algebraMap (𝓞 I.E) I.E (a j) = 0` using `congrArg Subtype.val hz`. Rewrite `h0` using `[ha j, Algebra.smul_def]`. Break down `mul_eq_zero.1 h0 with h1 | h1` into its components or cases. It suffices to derive a contradiction.

Establish `hd0 : (dd : 𝓞 I.E) ≠ 0` using `nonZeroDivisors.coe_ne_zero dd`. Conclude with `hd0 (by simpa using h1)`. Conclude with `h1`. Establish `hL_le : ∀ y ∈ I.L, y ∈ LA I p` using `fun y hy => Submodule.subset_span hy`. Establish `hclear : ∀ x : Fin I.n → I.E, ∃ d : 𝓞 I.E, d ≠ 0 ∧ ((d : I.E) • x) ∈ I.L`.

Introduce `x`. Take `⟨s, hs⟩` from `I.L_fg`. Establish `hx : x ∈ Submodule.span I.E (s : Set (Fin I.n → I.E))`. Establish `h1 : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤`. Rewrite using `[← I.L_span, ← hs, Submodule.span_span_of_tower]`.

Rewrite using `[h1]`. Conclude with `Submodule.mem_top`. Take `⟨c, hc⟩` from `(Submodule.mem_span_finset).1 hx`. Take `⟨dd, hdd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 I.E)) s c`. Use `choose a ha using hdd`.

Use `⟨dd, nonZeroDivisors.coe_ne_zero dd, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc.2, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun y hy => ?_` and prove the remaining obligations. Rewrite using `[smul_smul]`. Establish `h2 : ((dd : 𝓞 I.E) : I.E) * c y = algebraMap (𝓞 I.E) I.E (a y hy)`.

Rewrite using `[ha y hy, Algebra.smul_def]`. Rewrite using `[h2, algebraMap_smul]`. Conclude with `I.L.smul_mem _ (hs ▸ Submodule.subset_span hy)`. Set `b` to `Module.finBasis (Ap I p) (WA I p r e f)`. Establish `hspan : Submodule.span I.E (Set.range fun j => ((b j : WA I p r e f) : Fin I.n → I.E)) = LinearMap.ker φ`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `(hφ _).2 ((mem_WA I).mp (b j).2).2`. Introduce `x hx`.

Take `⟨d, hd, hdx⟩` from `hclear x`. Establish `hWA : (d : I.E) • x ∈ WA I p r e f`. Use `(mem_WA I).mpr ⟨hL_le _ hdx, fun a => ?_⟩` and prove the remaining obligations. Use `((hφ x).1 hx) a` as an intermediate fact. Rewrite using `[hG_smul_right, hG_smul_right, this.1, this.2, mul_zero]`.

Conclude with `⟨rfl, rfl⟩`. Establish `h1 : ((d : I.E) • x) ∈ Submodule.span (Ap I p) (Set.range fun j => ((b j : WA I p r e f) : Fin I.n → I.E))`. Establish `hm` using `b.mem_span (⟨(d : I.E) • x, hWA⟩ : WA I p r e f)`. Use `Submodule.apply_mem_span_image_of_mem_span (WA I p r e f).subtype hm` as an intermediate fact. Rewrite `this` using `[← Set.range_comp]`. Then use the resulting hypothesis.

Establish `h2` using `span_Ap_le I _ h1`. Establish `hdE : (d : I.E) ≠ 0` using `by simpa using hd`. Use `Submodule.smul_mem _ ((d : I.E)⁻¹) h2` as an intermediate fact. Rewrite `this` using `[smul_smul, inv_mul_cancel₀ hdE, one_smul]`. Then use the resulting hypothesis. Establish `hm : Module.finrank (Ap I p) (WA I p r e f) = k + 1`.

Establish `h1` using `(linearIndependent_iff_card_eq_finrank_span.1 (hLI b))`. Rewrite `h1` using `[Fintype.card_fin]`. Unfold `Set.finrank at h1`. Rewrite `h1` using `[hspan, hker]`. Conclude with `h1`.

Set `b'` to `b.reindex (finCongr hm)`. Use `⟨fun i => ((b' i : WA I p r e f) : Fin I.n → I.E), fun i => (mem_WA I).mp (b' i).2, hLI b', ?_⟩` and prove the remaining obligations. Introduce `x hxL hxo`. Establish `hWA : x ∈ WA I p r e f` using `(mem_WA I).mpr ⟨hxL, hxo⟩`. Establish `hm2` using `b'.mem_span (⟨x, hWA⟩ : WA I p r e f)`.

Use `Submodule.apply_mem_span_image_of_mem_span (WA I p r e f).subtype hm2` as an intermediate fact. Rewrite `this` using `[← Set.range_comp]`. Then use the resulting hypothesis.
-/
theorem weil_basis_existence : WBasis := by
  intro I p r k e f M hp hPID hn hee hff hef hM hMe
  haveI := hPID
  have hfe : ∀ a b, hG I (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hG_symm, hef]
    by_cases h : b = a
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h), star_zero]
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin r → I.E) × (Fin r → I.E) :=
    { toFun := fun x => (fun a => hG I (e a) x, fun a => hG I (f a) x)
      map_add' := fun x y => by
        refine Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;> simp [hG_add_right]
      map_smul' := fun c x => by
        refine Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;> simp [hG_smul_right] }
  have hφ : ∀ x, x ∈ LinearMap.ker φ ↔ ∀ a, hG I (e a) x = 0 ∧ hG I (f a) x = 0 := by
    intro x
    simp only [LinearMap.mem_ker, φ, LinearMap.coe_mk, AddHom.coe_mk, Prod.ext_iff, funext_iff,
      Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
    exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨s, t⟩
    refine ⟨∑ b, (s b • f b + t b • e b), ?_⟩
    refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · simp [φ, hG_sum_right, hG_add_right, hG_smul_right, hef, hee, Prod.fst_sum, Finset.sum_apply]
    · simp [φ, hG_sum_right, hG_add_right, hG_smul_right, hfe, hff, Prod.snd_sum, Finset.sum_apply]
  have hker : Module.finrank I.E (LinearMap.ker φ) = k + 1 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_prod, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h1
    omega
  have hNZ : NoZeroSMulDivisors (Ap I p) (WA I p r e f) := by
    refine ⟨fun {c x} h => ?_⟩
    have h2 : (c : I.E) • (x : Fin I.n → I.E) = 0 := by
      have := congrArg Subtype.val h
      simpa [smul_Ap] using this
    rcases smul_eq_zero.1 h2 with h3 | h3
    · left; exact Subtype.ext h3
    · right; exact Subtype.ext h3
  haveI := hNZ
  haveI := WA_finite I (p := p) e f
  haveI : Module.Free (Ap I p) (WA I p r e f) := Module.free_of_finite_type_torsion_free'
  have hLI : ∀ {ι : Type} [Fintype ι] (bb : Module.Basis ι (Ap I p) (WA I p r e f)),
      LinearIndependent I.E (fun j => ((bb j : WA I p r e f) : Fin I.n → I.E)) := by
    intro ι _ bb
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 I.E)) Finset.univ g
    choose a ha using fun i => hdd i (Finset.mem_univ i)
    have hsum : ∑ i, (⟨algebraMap (𝓞 I.E) I.E (a i), (Ap I p).algebraMap_mem (a i)⟩ : Ap I p) • bb i = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_Ap, ZeroMemClass.coe_zero]
      have : ∑ i, ((dd : 𝓞 I.E) : I.E) • (g i • ((bb i : WA I p r e f) : Fin I.n → I.E)) = 0 := by
        rw [← Finset.smul_sum, hg, smul_zero]
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, ha i, Algebra.smul_def]
      rfl
    have hz := (Fintype.linearIndependent_iff.1 bb.linearIndependent) _ hsum j
    have h0 : algebraMap (𝓞 I.E) I.E (a j) = 0 := congrArg Subtype.val hz
    rw [ha j, Algebra.smul_def] at h0
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exfalso
      have hd0 : (dd : 𝓞 I.E) ≠ 0 := nonZeroDivisors.coe_ne_zero dd
      exact hd0 (by simpa using h1)
    · exact h1
  have hL_le : ∀ y ∈ I.L, y ∈ LA I p := fun y hy => Submodule.subset_span hy
  have hclear : ∀ x : Fin I.n → I.E, ∃ d : 𝓞 I.E, d ≠ 0 ∧ ((d : I.E) • x) ∈ I.L := by
    intro x
    obtain ⟨s, hs⟩ := I.L_fg
    have hx : x ∈ Submodule.span I.E (s : Set (Fin I.n → I.E)) := by
      have h1 : Submodule.span I.E (s : Set (Fin I.n → I.E)) = ⊤ := by
        rw [← I.L_span, ← hs, Submodule.span_span_of_tower]
      rw [h1]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_finset).1 hx
    obtain ⟨dd, hdd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 I.E)) s c
    choose a ha using hdd
    refine ⟨dd, nonZeroDivisors.coe_ne_zero dd, ?_⟩
    rw [← hc.2, Finset.smul_sum]
    refine Submodule.sum_mem _ fun y hy => ?_
    rw [smul_smul]
    have h2 : ((dd : 𝓞 I.E) : I.E) * c y = algebraMap (𝓞 I.E) I.E (a y hy) := by
      rw [ha y hy, Algebra.smul_def]
    rw [h2, algebraMap_smul]
    exact I.L.smul_mem _ (hs ▸ Submodule.subset_span hy)
  let b := Module.finBasis (Ap I p) (WA I p r e f)
  have hspan : Submodule.span I.E (Set.range fun j => ((b j : WA I p r e f) : Fin I.n → I.E)) =
      LinearMap.ker φ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (hφ _).2 ((mem_WA I).mp (b j).2).2
    · intro x hx
      obtain ⟨d, hd, hdx⟩ := hclear x
      have hWA : (d : I.E) • x ∈ WA I p r e f := by
        refine (mem_WA I).mpr ⟨hL_le _ hdx, fun a => ?_⟩
        have := ((hφ x).1 hx) a
        rw [hG_smul_right, hG_smul_right, this.1, this.2, mul_zero]
        exact ⟨rfl, rfl⟩
      have h1 : ((d : I.E) • x) ∈ Submodule.span (Ap I p)
          (Set.range fun j => ((b j : WA I p r e f) : Fin I.n → I.E)) := by
        have hm := b.mem_span (⟨(d : I.E) • x, hWA⟩ : WA I p r e f)
        have := Submodule.apply_mem_span_image_of_mem_span (WA I p r e f).subtype hm
        rwa [← Set.range_comp] at this
      have h2 := span_Ap_le I _ h1
      have hdE : (d : I.E) ≠ 0 := by simpa using hd
      have := Submodule.smul_mem _ ((d : I.E)⁻¹) h2
      rwa [smul_smul, inv_mul_cancel₀ hdE, one_smul] at this
  have hm : Module.finrank (Ap I p) (WA I p r e f) = k + 1 := by
    have h1 := (linearIndependent_iff_card_eq_finrank_span.1 (hLI b))
    rw [Fintype.card_fin] at h1
    unfold Set.finrank at h1
    rw [hspan, hker] at h1
    exact h1
  let b' := b.reindex (finCongr hm)
  refine ⟨fun i => ((b' i : WA I p r e f) : Fin I.n → I.E), fun i => (mem_WA I).mp (b' i).2, hLI b', ?_⟩
  intro x hxL hxo
  have hWA : x ∈ WA I p r e f := (mem_WA I).mpr ⟨hxL, hxo⟩
  have hm2 := b'.mem_span (⟨x, hWA⟩ : WA I p r e f)
  have := Submodule.apply_mem_span_image_of_mem_span (WA I p r e f).subtype hm2
  rwa [← Set.range_comp] at this

end PI.ScRefExists.WB
