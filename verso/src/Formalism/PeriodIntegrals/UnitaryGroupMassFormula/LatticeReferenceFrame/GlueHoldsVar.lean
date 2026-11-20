import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeReferenceFrame.HGNsmulRight

noncomputable section

open NumberField Formalism.MainNotions.S
open scoped TensorProduct

namespace PI.ScRefExists.GlueC

open PI.ScRefExists PI.ScRefExists.GlueA PI.ScRefExists.GlueB PI.ScRefExists.Sk

/- English proof (translation)
Introduce `h1 h2 h3 h4`. Apply `PI.ScRefExists.UnitaryGroupMassFormula.target_of_two` to reduce the goal to its premises. Introduce `I g r k e f hg hs hn he hf hef hi`. Establish `hg1 : 1 ≤ g` using `by omega`. Establish `hc : ∀ x : Fin I.n → I.E, InAt I g 1 (incl I x) → ∃ c : ℕ, Nat.Coprime c g ∧ c • x ∈ I.L`.

Introduce and unpack `x ⟨c, hcg, hm⟩`. Use `⟨c, hcg, mem_L_of I h3 ?_⟩` and prove the remaining obligations. Rewrite using `[incl_nsmul, ← PI.ScRefExists.UnitaryGroupMassFormula.mL_one]`. Conclude with `hm`. Use `choose ce hce hceL using fun a => hc (e a) (hi a).1`.

Use `choose cf hcf hcfL using fun a => hc (f a) (hi a).2`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM, hMef⟩ : ∃ M : ℕ, Nat.Coprime M g ∧ ∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L := by`. Use `⟨∏ a, ce a * cf a, Nat.coprime_prod_left_iff.2 (fun a _ => Nat.Coprime.mul_left (hce a) (hcf a)), fun a => ?_⟩` and prove the remaining obligations. Take `⟨d, hd⟩ : ce a * cf a ∣ ∏ a, ce a * cf a` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ a)`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hd, show ce a * cf a * d = (cf a * d) * ce a by ring, mul_smul]`. Conclude with `nsmul_mem (hceL a) _`. Rewrite using `[hd, show ce a * cf a * d = (ce a * d) * cf a by ring, mul_smul]`. Conclude with `nsmul_mem (hcfL a) _`. Take `⟨Q, -, hQ⟩` from `Nat.exists_mul_mod_eq_one_of_coprime hM (by omega : 1 < g)`.

Take `⟨s, hN⟩ : ∃ s : ℕ, M * Q = 1 + g * s` from `⟨M * Q / g, by have := Nat.div_add_mod (M * Q) g; rw [hQ] at this; linarith⟩`. Establish `hNE : (M : I.E) * (Q : I.E) = 1 + (g : I.E) * (s : I.E)` using `by exact_mod_cast hN`. Take `⟨θ, hθ⟩` from `h1 I g hg1 hs`. Take `⟨ε, hεi, hεe, hεo, hεθ⟩` from `h2 I g θ hg1 hs hθ`. Take `⟨z, b, bd, hz, hb, hez, heb, hzz, hzb, hbb, hspan⟩` from `h4 I g r k θ e f M hg1 hs hθ hn he hf hef hM hMef`.

Simplify using `only [Sk.hG] at hez heb hzz hzb hbb`. Take `⟨t, ht, hεt⟩` from `id hεθ`. Take `⟨t', ht', hσt⟩` from `zmod_sig I g hεθ`. Use `⟨{ e0 := fun a => incl I (Q • M • e a) f0 := fun a => incl I (Q • M • f a) z0 := incl I z bw := fun i => ε • incl I (b i) bwd := fun i => sigA I ε • incl I (bd i) ew := ε vectorsInLattice := ?_ basisApprox := ?_ gramIntegral := ?_ formsAtZero := ?_ weightVectorsIntegral := ?_ ew_ …` and prove the remaining obligations. Conclude with `⟨fun a => ⟨incl_mem_Lf I (nsmul_mem (hMef a).1 Q), incl_mem_Lf I (nsmul_mem (hMef a).2 Q)⟩, incl_mem_Lf I hz, fun i => ⟨smul_mem_Lf I hεi (incl_mem_Lf I (hb i).1), smul_mem_Lf I (sigA_mem I hεi) (incl_mem_Lf I (hb i).2)⟩⟩`.

Introduce `a`. Establish `key : ∀ x : Fin I.n → I.E, M • x ∈ I.L → InAt I g g (incl I (Q • M • x) - incl I x)`. Introduce `x hx`. Use `⟨M, hM, ?_⟩` and prove the remaining obligations. Establish `h' : ((M : ℕ) : I.E ⊗[I.F] Af I.F) • (incl I (Q • M • x) - incl I x) = ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • x)`.

Rewrite using `[← incl_sub, ← incl_nsmul, ← incl_nsmul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul]`. Take the linear combination `((M : I.E) * x i) * hNE`.

Rewrite using `[h']`. Conclude with `mem_mL I g (incl_mem_Lf I (nsmul_mem hx s))`. Conclude with `⟨key _ (hMef a).1, key _ (hMef a).2⟩`. Introduce `a b'`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I (Q • M • e b')))`. Rewrite using `[hA_incl]`. Simplify using `only [hG_nsmul_left, hG_nsmul_right, he a b', mul_zero, map_zero]`. Conclude with `zmod_zero I g`. Use `show ZMod' I g (hA I (incl I (Q • M • f a)) (incl I (Q • M • f b')))`.

Rewrite using `[hA_incl]`. Simplify using `only [hG_nsmul_left, hG_nsmul_right, hf a b', mul_zero, map_zero]`. Conclude with `zmod_zero I g`. Use `show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I (Q • M • f b')) - if a = b' then 1 else 0)`. Rewrite using `[hA_incl]`.

Simplify using `only [hG_nsmul_left, hG_nsmul_right, hef a b']`. Use `split_ifs with hab`. Rewrite using `[mul_one, ← map_one (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_sub]`. Apply `zmod_of_GE` to reduce the goal to its premises. Apply `ge_of_nat I g (s * (M * Q + 1))` to reduce the goal to its premises.

Use `push_cast`. Take the linear combination `((M : I.E) * (Q : I.E) + 1) * hNE`. Simplify using `only [mul_zero, map_zero, sub_zero]`. Conclude with `zmod_zero I g`. Use `⟨?_, fun a => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Use `show ZMod' I g (hA I (incl I z) (incl I z) + 1)`. Rewrite using `[hA_incl, ← map_one (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_add]`. Conclude with `zmod_of_GE I g hzz`. Use `show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I z))`. Rewrite using `[hA_incl]`.

Simplify using `only [hG_nsmul_left, (hez a).1, mul_zero, map_zero]`. Conclude with `zmod_zero I g`. Use `show ZMod' I g (hA I (incl I (Q • M • f a)) (incl I z))`. Rewrite using `[hA_incl]`. Simplify using `only [hG_nsmul_left, (hez a).2, mul_zero, map_zero]`.

Conclude with `zmod_zero I g`. Introduce `i`. Use `⟨?_, ?_, fun a => ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Use `show ZMod' I g (hA I (incl I z) (ε • incl I (b i)))`. Rewrite using `[hA_smul_right, hA_incl]`.

Conclude with `zmod_eps I g hεθ (hG_int I hz (hb i).1) (hzb i).1`. Use `show ZMod' I g (hA I (incl I z) (sigA I ε • incl I (bd i)))`. Rewrite using `[hA_smul_right, hA_incl]`. Conclude with `zmod_eps I g (zmod_sig I g hεθ) (hG_int I hz (hb i).2) (hzb i).2`. Use `show ZMod' I g (hA I (incl I (Q • M • e a)) (ε • incl I (b i)))`.

Rewrite using `[hA_smul_right, hA_incl]`. Simplify using `only [hG_nsmul_left, (heb a i).1, mul_zero, map_zero]`. Conclude with `zmod_zero I g`. Use `show ZMod' I g (hA I (incl I (Q • M • f a)) (ε • incl I (b i)))`. Rewrite using `[hA_smul_right, hA_incl]`.

Simplify using `only [hG_nsmul_left, (heb a i).2.1, mul_zero, map_zero]`. Conclude with `zmod_zero I g`. Use `show ZMod' I g (hA I (incl I (Q • M • e a)) (sigA I ε • incl I (bd i)))`. Rewrite using `[hA_smul_right, hA_incl]`. Simplify using `only [hG_nsmul_left, (heb a i).2.2.1, mul_zero, map_zero]`.

Conclude with `zmod_zero I g`. Use `show ZMod' I g (hA I (incl I (Q • M • f a)) (sigA I ε • incl I (bd i)))`. Rewrite using `[hA_smul_right, hA_incl]`. Simplify using `only [hG_nsmul_left, (heb a i).2.2.2, mul_zero, map_zero]`. Conclude with `zmod_zero I g`.

Introduce `y hy`. Take `⟨u, hu⟩` from `hθ.2.2`. Establish `e1 : 1 - ε - sigA I ε = ((g : ℕ) : I.E ⊗[I.F] Af I.F) * (Formalism.UG.inclE (F` using `I.F) (Af I.F) (u : I.E) - t - t') := by`. Establish `hu'` using `congrArg (Formalism.UG.inclE (F := I.F) (Af I.F)) hu`. Rewrite `hu'` using `[map_sub, map_sub, map_one, map_mul, map_natCast]`.

Take the linear combination `hu' - hεt - hσt`. Rewrite using `[e1, mul_smul]`. Conclude with `mem_mL I g (smul_mem_Lf I (sub_mem (sub_mem (inclE_mem' I u) ht) ht') hy)`. Introduce `i show ε • incl I (b i) = ε • ε • incl I (b i)`. Rewrite using `[smul_smul, hεe]`.

Introduce `i show sigA I ε • incl I (bd i) = sigA I ε • sigA I ε • incl I (bd i)`. Rewrite using `[smul_smul, ← map_mul, hεe]`. Introduce `i j show ZMod' I g (hA I (sigA I ε • incl I (bd i)) (ε • incl I (b j)) - if i = j then ε else 0)`. Rewrite using `[hA_smul_left, hA_smul_right, sigA_sigA, hA_incl]`. Establish `e2 : ε * (ε * Formalism.UG.inclE (F` using `I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J (bd i) (b j))) - (if i = j then ε else 0) = ε * Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J (bd i) (b j) - if i = j then 1 else 0) := by split_ifs`.

Rewrite using `[map_sub, map_one, ← mul_assoc, hεe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sub_zero, sub_zero, ← mul_assoc, hεe]`. Rewrite using `[e2]`. Use `zmod_eps I g hεθ (sub_mem (hG_int I (hb i).2 (hb j).1) ?_) (hbb i j)` and prove the remaining obligations.

Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Introduce `y hy`. Set `S : Set (VA I)` to `Set.range (fun a => incl I (Q • M • e a)) ∪ Set.range (fun a => incl I (Q • M • f a)) ∪ {incl I z} ∪ Set.range (fun i => ε • incl I (b i)) ∪ Set.range (fun i => sigA I ε • incl I (bd i))`.

Use `show y ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g`. Establish `hSe : ∀ a, incl I (Q • M • e a) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g` using `fun a => Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))`. Establish `hSf : ∀ a, incl I (Q • M • f a) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g` using `fun a => Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))))`. Establish `hSz : incl I z ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g` using `Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inr rfl))))`. Establish `hSb : ∀ i, ε • incl I (b i) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g` using `fun i => Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))`.

Establish `hSbd : ∀ i, sigA I ε • incl I (bd i) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g` using `fun i => Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩))`. Set `T : Submodule (𝓞 I.E) (Fin I.n → I.E)` to `{ carrier := {x | incl I x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g} add_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_ofPred_eq, incl_add] at *`. Conclude with `add_mem hx hy`. Use the proof step `zero_mem' := by`.

Simplify using `only [Set.mem_ofPred_eq, incl_zero]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c x hx => by`. Simplify using `only [Set.mem_ofPred_eq] at *`. Rewrite using `[incl_osmul]`.

Conclude with `Submodule.smul_mem _ _ hx }`. Establish `memT : ∀ x, incl I x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g → x ∈ T` using `fun x h => h`. Establish `hgT : gL I g ≤ T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `memT _ ?_` and prove the remaining obligations. Rewrite using `[incl_smul, ← natCast_eq]`. Conclude with `Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I hx))`. Establish `hST : Submodule.span (𝓞 I.E) (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪ {z} ∪ Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ≤ T`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩)`. Use `memT _ ?_` and prove the remaining obligations. Establish `h' : incl I (M • e a) = M • incl I (Q • M • e a) - ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • e a)`. Rewrite using `[← incl_nsmul', ← incl_nsmul, ← incl_sub]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul]`. Take the linear combination `(-(M : I.E) * e a i) * hNE`. Rewrite using `[h']`. Conclude with `sub_mem (nsmul_mem (hSe a) M) (Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I (nsmul_mem (hMef a).1 s))))`.

Use `memT _ ?_` and prove the remaining obligations. Establish `h' : incl I (M • f a) = M • incl I (Q • M • f a) - ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • f a)`. Rewrite using `[← incl_nsmul', ← incl_nsmul, ← incl_sub]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul]`. Take the linear combination `(-(M : I.E) * f a i) * hNE`. Rewrite using `[h']`. Conclude with `sub_mem (nsmul_mem (hSf a) M) (Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I (nsmul_mem (hMef a).2 s))))`. Conclude with `memT _ hSz`.

Use `memT _ ?_` and prove the remaining obligations. Establish `h' : incl I ((θ : I.E) • b i) = ε • incl I (b i) - ((g : ℕ) : I.E ⊗[I.F] Af I.F) • (t • incl I (b i))`. Rewrite using `[incl_smul, smul_smul, ← sub_smul]`. Use `congr 1`. Take the linear combination `-hεt`.

Rewrite using `[h']`. Conclude with `sub_mem (hSb i) (Submodule.mem_sup_right (mem_mL I g (smul_mem_Lf I ht (incl_mem_Lf I (hb i).1))))`. Use `memT _ ?_` and prove the remaining obligations. Establish `h' : incl I (star (θ : I.E) • bd i) = sigA I ε • incl I (bd i) - ((g : ℕ) : I.E ⊗[I.F] Af I.F) • (t' • incl I (bd i))`. Rewrite using `[incl_smul, smul_smul, ← sub_smul]`.

Use `congr 1`. Take the linear combination `-hσt`. Rewrite using `[h']`. Conclude with `sub_mem (hSbd i) (Submodule.mem_sup_right (mem_mL I g (smul_mem_Lf I ht' (incl_mem_Lf I (hb i).2))))`. Establish `hLT : I.Lf ≤ Submodule.span (IntAf I.F I.E) S ⊔ mL I g`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨x, hx⟩, rfl⟩`. Use `show incl I x ∈ _`. Conclude with `(sup_le hST hgT) (hspan x hx)`. Conclude with `hLT hy`.
-/
theorem glue_holds_var : Glue := by
  intro h1 h2 h3 h4
  apply PI.ScRefExists.UnitaryGroupMassFormula.target_of_two
  intro I g r k e f hg hs hn he hf hef hi
  have hg1 : 1 ≤ g := by omega
  have hc : ∀ x : Fin I.n → I.E, InAt I g 1 (incl I x) → ∃ c : ℕ, Nat.Coprime c g ∧ c • x ∈ I.L := by
    rintro x ⟨c, hcg, hm⟩
    refine ⟨c, hcg, mem_L_of I h3 ?_⟩
    rw [incl_nsmul, ← PI.ScRefExists.UnitaryGroupMassFormula.mL_one]
    exact hm
  choose ce hce hceL using fun a => hc (e a) (hi a).1
  choose cf hcf hcfL using fun a => hc (f a) (hi a).2
  obtain ⟨M, hM, hMef⟩ : ∃ M : ℕ, Nat.Coprime M g ∧ ∀ a, M • e a ∈ I.L ∧ M • f a ∈ I.L := by
    refine ⟨∏ a, ce a * cf a, Nat.coprime_prod_left_iff.2 (fun a _ => Nat.Coprime.mul_left (hce a) (hcf a)),
      fun a => ?_⟩
    obtain ⟨d, hd⟩ : ce a * cf a ∣ ∏ a, ce a * cf a := Finset.dvd_prod_of_mem _ (Finset.mem_univ a)
    constructor
    · rw [hd, show ce a * cf a * d = (cf a * d) * ce a by ring, mul_smul]
      exact nsmul_mem (hceL a) _
    · rw [hd, show ce a * cf a * d = (ce a * d) * cf a by ring, mul_smul]
      exact nsmul_mem (hcfL a) _
  obtain ⟨Q, -, hQ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hM (by omega : 1 < g)
  obtain ⟨s, hN⟩ : ∃ s : ℕ, M * Q = 1 + g * s :=
    ⟨M * Q / g, by have := Nat.div_add_mod (M * Q) g; rw [hQ] at this; linarith⟩
  have hNE : (M : I.E) * (Q : I.E) = 1 + (g : I.E) * (s : I.E) := by exact_mod_cast hN
  obtain ⟨θ, hθ⟩ := h1 I g hg1 hs
  obtain ⟨ε, hεi, hεe, hεo, hεθ⟩ := h2 I g θ hg1 hs hθ
  obtain ⟨z, b, bd, hz, hb, hez, heb, hzz, hzb, hbb, hspan⟩ :=
    h4 I g r k θ e f M hg1 hs hθ hn he hf hef hM hMef
  simp only [Sk.hG] at hez heb hzz hzb hbb
  obtain ⟨t, ht, hεt⟩ := id hεθ
  obtain ⟨t', ht', hσt⟩ := zmod_sig I g hεθ
  refine ⟨{
    e0 := fun a => incl I (Q • M • e a)
    f0 := fun a => incl I (Q • M • f a)
    z0 := incl I z
    bw := fun i => ε • incl I (b i)
    bwd := fun i => sigA I ε • incl I (bd i)
    ew := ε
    vectorsInLattice := ?_
    basisApprox := ?_
    gramIntegral := ?_
    formsAtZero := ?_
    weightVectorsIntegral := ?_
    ew_idem := hεe
    ew_orth := hεo
    ew_int := hεi
    ew_full := ?_
    bw_w := ?_
    bwd_w := ?_
    bw_dual := ?_
    latticeSpan := ?_ }⟩
  · exact ⟨fun a => ⟨incl_mem_Lf I (nsmul_mem (hMef a).1 Q), incl_mem_Lf I (nsmul_mem (hMef a).2 Q)⟩,
      incl_mem_Lf I hz, fun i => ⟨smul_mem_Lf I hεi (incl_mem_Lf I (hb i).1),
        smul_mem_Lf I (sigA_mem I hεi) (incl_mem_Lf I (hb i).2)⟩⟩
  · intro a
    have key : ∀ x : Fin I.n → I.E, M • x ∈ I.L → InAt I g g (incl I (Q • M • x) - incl I x) := by
      intro x hx
      refine ⟨M, hM, ?_⟩
      have h' : ((M : ℕ) : I.E ⊗[I.F] Af I.F) • (incl I (Q • M • x) - incl I x) =
          ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • x) := by
        rw [← incl_sub, ← incl_nsmul, ← incl_nsmul]
        congr 1
        funext i
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul]
        linear_combination ((M : I.E) * x i) * hNE
      rw [h']
      exact mem_mL I g (incl_mem_Lf I (nsmul_mem hx s))
    exact ⟨key _ (hMef a).1, key _ (hMef a).2⟩
  · intro a b'
    refine ⟨?_, ?_, ?_⟩
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I (Q • M • e b')))
      rw [hA_incl]
      simp only [hG_nsmul_left, hG_nsmul_right, he a b', mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (incl I (Q • M • f b')))
      rw [hA_incl]
      simp only [hG_nsmul_left, hG_nsmul_right, hf a b', mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I (Q • M • f b')) - if a = b' then 1 else 0)
      rw [hA_incl]
      simp only [hG_nsmul_left, hG_nsmul_right, hef a b']
      split_ifs with hab
      · rw [mul_one, ← map_one (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_sub]
        apply zmod_of_GE
        apply ge_of_nat I g (s * (M * Q + 1))
        push_cast
        linear_combination ((M : I.E) * (Q : I.E) + 1) * hNE
      · simp only [mul_zero, map_zero, sub_zero]
        exact zmod_zero I g
  · refine ⟨?_, fun a => ⟨?_, ?_⟩⟩
    · show ZMod' I g (hA I (incl I z) (incl I z) + 1)
      rw [hA_incl, ← map_one (Formalism.UG.inclE (F := I.F) (Af I.F)), ← map_add]
      exact zmod_of_GE I g hzz
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (incl I z))
      rw [hA_incl]
      simp only [hG_nsmul_left, (hez a).1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (incl I z))
      rw [hA_incl]
      simp only [hG_nsmul_left, (hez a).2, mul_zero, map_zero]
      exact zmod_zero I g
  · intro i
    refine ⟨?_, ?_, fun a => ⟨?_, ?_, ?_, ?_⟩⟩
    · show ZMod' I g (hA I (incl I z) (ε • incl I (b i)))
      rw [hA_smul_right, hA_incl]
      exact zmod_eps I g hεθ (hG_int I hz (hb i).1) (hzb i).1
    · show ZMod' I g (hA I (incl I z) (sigA I ε • incl I (bd i)))
      rw [hA_smul_right, hA_incl]
      exact zmod_eps I g (zmod_sig I g hεθ) (hG_int I hz (hb i).2) (hzb i).2
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (ε • incl I (b i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (ε • incl I (b i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).2.1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • e a)) (sigA I ε • incl I (bd i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).2.2.1, mul_zero, map_zero]
      exact zmod_zero I g
    · show ZMod' I g (hA I (incl I (Q • M • f a)) (sigA I ε • incl I (bd i)))
      rw [hA_smul_right, hA_incl]
      simp only [hG_nsmul_left, (heb a i).2.2.2, mul_zero, map_zero]
      exact zmod_zero I g
  · intro y hy
    obtain ⟨u, hu⟩ := hθ.2.2
    have e1 : 1 - ε - sigA I ε = ((g : ℕ) : I.E ⊗[I.F] Af I.F) *
        (Formalism.UG.inclE (F := I.F) (Af I.F) (u : I.E) - t - t') := by
      have hu' := congrArg (Formalism.UG.inclE (F := I.F) (Af I.F)) hu
      rw [map_sub, map_sub, map_one, map_mul, map_natCast] at hu'
      linear_combination hu' - hεt - hσt
    rw [e1, mul_smul]
    exact mem_mL I g (smul_mem_Lf I (sub_mem (sub_mem (inclE_mem' I u) ht) ht') hy)
  · intro i
    show ε • incl I (b i) = ε • ε • incl I (b i)
    rw [smul_smul, hεe]
  · intro i
    show sigA I ε • incl I (bd i) = sigA I ε • sigA I ε • incl I (bd i)
    rw [smul_smul, ← map_mul, hεe]
  · intro i j
    show ZMod' I g (hA I (sigA I ε • incl I (bd i)) (ε • incl I (b j)) - if i = j then ε else 0)
    rw [hA_smul_left, hA_smul_right, sigA_sigA, hA_incl]
    have e2 : ε * (ε * Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J (bd i) (b j))) -
        (if i = j then ε else 0) = ε * Formalism.UG.inclE (F := I.F) (Af I.F)
          (Formalism.UG.hform (starRingEnd I.E) I.J (bd i) (b j) - if i = j then 1 else 0) := by
      split_ifs
      · rw [map_sub, map_one, ← mul_assoc, hεe]; ring
      · rw [sub_zero, sub_zero, ← mul_assoc, hεe]
    rw [e2]
    refine zmod_eps I g hεθ (sub_mem (hG_int I (hb i).2 (hb j).1) ?_) (hbb i j)
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro y hy
    let S : Set (VA I) := Set.range (fun a => incl I (Q • M • e a)) ∪
      Set.range (fun a => incl I (Q • M • f a)) ∪ {incl I z} ∪ Set.range (fun i => ε • incl I (b i)) ∪
      Set.range (fun i => sigA I ε • incl I (bd i))
    show y ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g
    have hSe : ∀ a, incl I (Q • M • e a) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun a =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl ⟨a, rfl⟩)))))
    have hSf : ∀ a, incl I (Q • M • f a) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun a =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, rfl⟩)))))
    have hSz : incl I z ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g :=
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inl (Or.inr rfl))))
    have hSb : ∀ i, ε • incl I (b i) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun i =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩)))
    have hSbd : ∀ i, sigA I ε • incl I (bd i) ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := fun i =>
      Submodule.mem_sup_left (Submodule.subset_span (Or.inr ⟨i, rfl⟩))
    let T : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
      { carrier := {x | incl I x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_ofPred_eq, incl_add] at *
          exact add_mem hx hy
        zero_mem' := by
          simp only [Set.mem_ofPred_eq, incl_zero]
          exact zero_mem _
        smul_mem' := fun c x hx => by
          simp only [Set.mem_ofPred_eq] at *
          rw [incl_osmul]
          exact Submodule.smul_mem _ _ hx }
    have memT : ∀ x, incl I x ∈ Submodule.span (IntAf I.F I.E) S ⊔ mL I g → x ∈ T := fun x h => h
    have hgT : gL I g ≤ T := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨x, hx, rfl⟩
      refine memT _ ?_
      rw [incl_smul, ← natCast_eq]
      exact Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I hx))
    have hST : Submodule.span (𝓞 I.E) (Set.range (fun a => M • e a) ∪ Set.range (fun a => M • f a) ∪
        {z} ∪ Set.range (fun i => (θ : I.E) • b i) ∪ Set.range (fun i => star (θ : I.E) • bd i)) ≤ T := by
      refine Submodule.span_le.2 ?_
      rintro _ ((((⟨a, rfl⟩ | ⟨a, rfl⟩) | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine memT _ ?_
        have h' : incl I (M • e a) = M • incl I (Q • M • e a) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • e a) := by
          rw [← incl_nsmul', ← incl_nsmul, ← incl_sub]
          congr 1
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul]
          linear_combination (-(M : I.E) * e a i) * hNE
        rw [h']
        exact sub_mem (nsmul_mem (hSe a) M)
          (Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I (nsmul_mem (hMef a).1 s))))
      · refine memT _ ?_
        have h' : incl I (M • f a) = M • incl I (Q • M • f a) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • incl I (s • M • f a) := by
          rw [← incl_nsmul', ← incl_nsmul, ← incl_sub]
          congr 1
          funext i
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.natCast_apply, nsmul_eq_mul]
          linear_combination (-(M : I.E) * f a i) * hNE
        rw [h']
        exact sub_mem (nsmul_mem (hSf a) M)
          (Submodule.mem_sup_right (mem_mL I g (incl_mem_Lf I (nsmul_mem (hMef a).2 s))))
      · exact memT _ hSz
      · refine memT _ ?_
        have h' : incl I ((θ : I.E) • b i) = ε • incl I (b i) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • (t • incl I (b i)) := by
          rw [incl_smul, smul_smul, ← sub_smul]
          congr 1
          linear_combination -hεt
        rw [h']
        exact sub_mem (hSb i)
          (Submodule.mem_sup_right (mem_mL I g (smul_mem_Lf I ht (incl_mem_Lf I (hb i).1))))
      · refine memT _ ?_
        have h' : incl I (star (θ : I.E) • bd i) = sigA I ε • incl I (bd i) -
            ((g : ℕ) : I.E ⊗[I.F] Af I.F) • (t' • incl I (bd i)) := by
          rw [incl_smul, smul_smul, ← sub_smul]
          congr 1
          linear_combination -hσt
        rw [h']
        exact sub_mem (hSbd i)
          (Submodule.mem_sup_right (mem_mL I g (smul_mem_Lf I ht' (incl_mem_Lf I (hb i).2))))
    have hLT : I.Lf ≤ Submodule.span (IntAf I.F I.E) S ⊔ mL I g := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      show incl I x ∈ _
      exact (sup_le hST hgT) (hspan x hx)
    exact hLT hy

end PI.ScRefExists.GlueC

end
