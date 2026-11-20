import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMapEqOfKerEq

open Module GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model GlobalTheory.UPel.Sm.KSCount

noncomputable section

namespace GlobalTheory.UPel.Sm.KSCount

/- English proof (translation)
Introduce `k H O _ _ _ _ _ ρ st φ Fil Z w r r' d hst hadj hskew hnd hiso hdim hstab hcomm hA hr hφw hZ hd`. Use `set A := ρ w with hAdef`. Establish `hA2 : ∀ x, A (A x) = (r + r') • A x - (r * r') • x`. Introduce `x`. Establish `h` using `LinearMap.congr_fun hA x`.

Simplify using `only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, LinearMap.zero_apply] at h`. Take the linear combination `(norm := module) h`. Establish `hrr : r - r' ≠ 0` using `sub_ne_zero.2 hr`. Use `set c := (r - r')⁻¹ with hc`. Establish `hc1 : c * (r - r') = 1` using `inv_mul_cancel₀ hrr`.

Set `P : Module.End k H` to `c • (A - r' • 1)`. Establish `hPx : ∀ x, P x = c • (A x - r' • x)` using `fun x => by simp [P]`. Establish `hPA : ∀ x, A (P x) = r • P x`. Introduce `x`. Rewrite using `[hPx, map_smul, map_sub, map_smul, hA2]`.

Take the linear combination `(norm := module) (0:k) • x`. Establish `hPfix : ∀ x, A x = r • x → P x = x`. Introduce `x hx`. Rewrite using `[hPx, hx]`. Take the linear combination `(norm := module) hc1 • x`.

Establish `hPkill : ∀ x, A x = r' • x → P x = 0`. Introduce `x hx`. Rewrite using `[hPx, hx]`. Simplify using the standard rewrite rules. Establish `hQA : ∀ x, A (x - P x) = r' • (x - P x)`.

Introduce `x`. Rewrite using `[map_sub, hPA]`. Establish `: A x - r' • x = (r - r') • P x` using `by rw [hPx, smul_smul, mul_comm, hc1, one_smul]`. Take the linear combination `(norm := module) this`. Establish `hPP : ∀ x, P (P x) = P x` using `fun x => hPfix _ (hPA x)`.

Establish `hPQ : ∀ x, P (x - P x) = 0` using `fun x => hPkill _ (hQA x)`. Establish `hAρ : ∀ a x, A (ρ a x) = ρ a (A x)` using `fun a x => LinearMap.congr_fun (hcomm a) x`. Establish `hPρ : ∀ a x, P (ρ a x) = ρ a (P x)`. Introduce `a x`. Rewrite using `[hPx, hPx, hAρ, map_smul, map_sub, map_smul]`.

Establish `hPFil : ∀ x ∈ Fil, P x ∈ Fil` using `fun x hx => by`. Rewrite using `[hPx]`. Conclude with `Fil.smul_mem _ (Fil.sub_mem (hstab w x hx) (Fil.smul_mem _ hx))`. Establish `hQFil : ∀ x ∈ Fil, x - P x ∈ Fil` using `fun x hx => Fil.sub_mem hx (hPFil x hx)`. Establish `hφeig : ∀ (s t : k), s ≠ t → s + t = r + r' → ∀ u v, A u = s • u → A v = s • v → φ u v = 0`.

Introduce `s t hst' hsum u v hu hv`. Establish `h` using `hφw u v`. Rewrite `h` using `[hu, hv]`. Simplify using `only [map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, smul_eq_mul] at h`. Establish `h2 : (s - t) * φ u v = 0` using `by linear_combination h - (φ u v) * hsum`.

Conclude with `(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hst')`. Establish `hφPP : ∀ x y, φ (P x) (P y) = 0` using `fun x y => hφeig r r' hr rfl _ _ (hPA x) (hPA y)`. Establish `hφQQ : ∀ x y, φ (x - P x) (y - P y) = 0` using `fun x y => hφeig r' r (Ne.symm hr) (add_comm _ _) _ _ (hQA x) (hQA y)`. Establish `hφdec : ∀ a b, φ a b = φ (P a) (b - P b) + φ (a - P a) (P b)`. Introduce `a b`.

Establish `e : φ a b = φ (P a + (a - P a)) (P b + (b - P b))` using `by simp`. Rewrite using `[e]`. Simplify using `only [map_add, LinearMap.add_apply, hφPP, hφQQ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnd' : φ.Nondegenerate` using `⟨hnd, fun y h => hnd y (fun x => by rw [hskew, h x, neg_zero])⟩`.

Establish `hperp : ∀ v, (∀ y ∈ Fil, φ v y = 0) → v ∈ Fil`. Establish `hle : Fil ≤ φ.orthogonal Fil`. Introduce `x hx`. Rewrite using `[LinearMap.BilinForm.mem_orthogonal_iff]`. Introduce `y hy`.

Conclude with `hiso y hy x hx`. Establish `hdim2` using `LinearMap.BilinForm.finrank_orthogonal hnd' Fil`. Establish `heq : Fil = φ.orthogonal Fil` using `Submodule.eq_of_le_of_finrank_le hle (by omega)`. Introduce `v hv`. Rewrite using `[heq, LinearMap.BilinForm.mem_orthogonal_iff]`.

Introduce `y hy`. Express the relevant statement in the definitionally equal form `φ y v = 0`. Rewrite using `[hskew, hv y hy, neg_zero]`. Establish `hAP : ∀ v, A v - r' • v = (r - r') • P v` using `fun v => by`. Rewrite using `[hPx, smul_smul, mul_comm, hc1, one_smul]`.

Establish `hPAc : ∀ x, P (A x) = A (P x)` using `fun x => by rw [hPx, hPx, map_smul, map_sub, map_smul]`. Use `set G := Fil ⊔ LinearMap.range (A - r • 1) with hG`. Establish `hrangeP : ∀ y ∈ LinearMap.range (A - r • 1), P y = 0`. Introduce and unpack `_ ⟨z, rfl⟩`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hPAc, hPA, sub_self]`.

Establish `hFilG : Fil ≤ G` using `le_sup_left`. Establish `hmemG : ∀ x ∈ G, P x ∈ Fil`. Introduce `x hx`. Take `⟨f, hf, y, hy, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add, hrangeP y hy, add_zero]`.

Conclude with `hPFil f hf`. Establish `hQG : ∀ x, x - P x ∈ G`. Introduce `x`. Apply `Submodule.mem_sup_right` to reduce the goal to its premises. Use `⟨(-c) • x, ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]`. Establish `h` using `hAP x`. Take the linear combination `(norm := module) (-c) • h - hc1 • P x + hc1 • x`. Establish `hZP : ∀ z ∈ Z, P z = z`. Introduce `z hz`.

Take `⟨y, rfl⟩` from `hZ hz`. Apply `hPfix` to reduce the goal to its premises. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hA2]`. Use `module`. Establish `hwQ : ∀ (F : Submodule k H) v, r • v - A v ∈ F → v - P v ∈ F`.

Introduce `F v hv`. Establish `e : v - P v = c • (r • v - A v)`. Establish `h` using `hAP v`. Take the linear combination `(norm := module) c • h - hc1 • v + hc1 • P v`. Rewrite using `[e]`.

Conclude with `F.smul_mem _ hv`. Establish `hwP : ∀ (F : Submodule k H) v, r' • v - A v ∈ F → P v ∈ F`. Introduce `F v hv`. Establish `e : P v = (-c) • (r' • v - A v)`. Establish `h` using `hAP v`.

Take the linear combination `(norm := module) (-c) • h - hc1 • P v`. Rewrite using `[e]`. Conclude with `F.smul_mem _ hv`. Establish `L1 : ∀ v y, φ (P v) y = φ (P v) (y - P y)` using `fun v y => by`. Rewrite using `[hφdec (P v) y]`.

Simplify using `[hPP]`. Establish `L2 : ∀ v y, φ (v - P v) y = φ v (P y)` using `fun v y => by`. Rewrite using `[hφdec (v - P v) y, hφdec v (P y)]`. Simplify using `[hPP, hPQ]`. Establish `L3 : ∀ x v, φ x (P v) = φ (x - P x) (P v)` using `fun x v => by`.

Rewrite using `[hφdec x (P v)]`. Simplify using `[hPP]`. Establish `L4 : ∀ x v, φ x (v - P v) = φ (P x) v` using `fun x v => by`. Rewrite using `[hφdec x (v - P v), hφdec (P x) v]`. Simplify using `[hPP, hPQ]`.

Establish `hQcrit : ∀ v, (∀ y ∈ Fil, φ v (P y) = 0) → v - P v ∈ Fil`. Introduce `v hv`. Apply `hperp` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[L2]`.

Conclude with `hv y hy`. Set `conj : (H →ₗ[k] H) →ₗ[k] (H →ₗ[k] H)` to `{ toFun := fun g => P ∘ₗ g ∘ₗ P map_add' := fun f g => by ext; simp map_smul' := fun a f => by ext; simp }`. Establish `hconj : ∀ g x, conj g x = P (g (P x))` using `fun _ _ => rfl`. Establish `hi : ∀ g, IsKS ρ φ Fil Z g → IsKS ρ 0 G Z (conj g)`. Introduce `g hg`.

Use `⟨fun a x hx => ?_, fun x hx => ?_, fun x _ y _ => by simp⟩` and prove the remaining obligations. Rewrite using `[hconj, hconj, hPρ a x, ← hPρ a (g (P x)), ← map_sub]`. Conclude with `hFilG (hPFil _ (hg.1 a _ (hmemG x hx)))`. Rewrite using `[hconj, hZP x hx]`. Conclude with `hFilG (hPFil _ (hg.2.1 x hx))`.

Establish `hker : ∀ g, IsKS ρ φ Fil Z g → ((∀ x ∈ Fil, g x ∈ Fil) ↔ (∀ x ∈ G, conj g x ∈ G))`. Introduce `g hg`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Rewrite using `[hconj]`.

Conclude with `hFilG (hPFil _ (h _ (hmemG x hx)))`. Introduce `h`. Establish `hPpart : ∀ u ∈ Fil, P (g (P u)) ∈ Fil`. Introduce `u hu`. Use `hmemG _ (h (P u) (hFilG (hPFil u hu)))` as an intermediate fact.

Rewrite `this` using `[hconj, hPP, hPP]`. Then use the resulting hypothesis. Establish `hgP : ∀ u ∈ Fil, g (P u) ∈ Fil`. Introduce `u hu`. Establish `hq : g (P u) - P (g (P u)) ∈ Fil`. Apply `hwQ` to reduce the goal to its premises.

Use `hg.1 w (P u) (hPFil u hu)` as an intermediate fact. Rewrite `this` using `[← hAdef, hPA, map_smul]`. Then use the resulting hypothesis. Use `Fil.add_mem hq (hPpart u hu)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `x hx`.

Establish `hu : x - P x ∈ Fil` using `hQFil x hx`. Establish `hp : P (g (x - P x)) ∈ Fil`. Apply `hwP` to reduce the goal to its premises. Use `hg.1 w (x - P x) hu` as an intermediate fact. Rewrite `this` using `[← hAdef, hQA, map_smul]`. Then use the resulting hypothesis.

Establish `hq : g (x - P x) - P (g (x - P x)) ∈ Fil`. Apply `hQcrit` to reduce the goal to its premises. Introduce `y hy`. Establish `h1` using `hg.2.2 (x - P x) hu (P y) (hPFil y hy)`. Establish `h2` using `hiso (x - P x) hu _ (hgP y hy)`.

Take the linear combination `h1 - h2`. Establish `e : g x = g (P x) + (P (g (x - P x)) + (g (x - P x) - P (g (x - P x))))`. Rewrite using `[add_sub_cancel, ← map_add, add_sub_cancel]`. Rewrite using `[e]`. Conclude with `Fil.add_mem (hgP x hx) (Fil.add_mem hp hq)`.

Establish `hiii : ∀ f', IsKS ρ 0 G Z f' → ∃ g, IsKS ρ φ Fil Z g ∧ ∀ x ∈ G, conj g x - f' x ∈ G`. Introduce `f' hf'`. Establish `hinj : Function.Injective φ.flip`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`.

Apply `hnd v` to reduce the goal to its premises. Introduce `u`. Rewrite using `[hskew]`. Establish `: φ u v = 0` using `LinearMap.congr_fun hv u`. Rewrite using `[this, neg_zero]`.

Establish `hsurj : Function.Surjective φ.flip` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj`. Take `⟨s, hs⟩` from `LinearMap.exists_rightInverse_of_surjective φ.flip (LinearMap.range_eq_top.2 hsurj)`. Set `L : H →ₗ[k] H` to `P ∘ₗ f' ∘ₗ P`. Set `T : H →ₗ[k] H` to `s ∘ₗ (-(L.dualMap ∘ₗ φ.flip))`. Establish `hT : ∀ u v, φ u (T v) = -φ (P (f' (P u))) v`.

Introduce `u v`. Use `LinearMap.congr_fun (LinearMap.congr_fun hs (-(L.dualMap ∘ₗ φ.flip) v)) u` as an intermediate fact. Simplify `this` using `[T, L]`. Set `g : H →ₗ[k] H` to `L + (1 - P) ∘ₗ T ∘ₗ (1 - P)`. Establish `hg : ∀ x, g x = P (f' (P x)) + (T (x - P x) - P (T (x - P x)))` using `fun x => by`.

Simplify using `[g, L]`. Establish `hT0 : T 0 = 0` using `map_zero T`. Use `⟨g, ⟨fun a x hx => ?_, fun z hz => ?_, fun x _ y _ => ?_⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩ : ∃ q, q = x - P x` from `⟨_, rfl⟩`. Take `⟨e, he⟩ : ∃ e, e = T (ρ a q) - ρ a (T q)` from `⟨_, rfl⟩`.

Establish `hqF : q ∈ Fil` using `hq ▸ hQFil x hx`. Establish `eq : g (ρ a x) - ρ a (g x) = P (f' (ρ a (P x)) - ρ a (f' (P x))) + (e - P e)`. Establish `hq' : ρ a x - P (ρ a x) = ρ a q` using `by rw [hq, hPρ, ← map_sub]`. Rewrite using `[hg, hg, hq', he, ← hq]`. Simplify using `only [hPρ, map_sub, map_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[eq]`. Use `Fil.add_mem (hmemG _ (hf'.1 a _ (hFilG (hPFil x hx)))) (hQcrit e fun y hy => ?_)` and prove the remaining obligations. Use `set u := P y with hu`. Use `set t := T q with ht`.

Establish `hm : P (f' (ρ (st a) u)) - ρ (st a) (P (f' u)) ∈ Fil`. Rewrite using `[← hPρ (st a) (f' u), ← map_sub]`. Conclude with `hmemG _ (hf'.1 (st a) u (hFilG (hPFil y hy)))`. Establish `h4` using `hiso _ hm q hqF`. Rewrite `h4` using `[LinearMap.map_sub₂]`.

Establish `F2 : φ u (T (ρ a q)) = -φ (P (f' u)) (ρ a q)` using `by rw [hT, hu, hPP]`. Establish `F5 : φ (ρ (st a) u) t = -φ (P (f' (ρ (st a) u))) q` using `by rw [ht, hT, hu, hPρ, hPP]`. Establish `F3` using `hadj a t u`. Establish `F7` using `hadj a q (P (f' u))`. Establish `S1` using `hskew (T (ρ a q)) u`.

Establish `S2` using `hskew t (ρ (st a) u)`. Establish `S3` using `hskew (P (f' u)) (ρ a q)`. Establish `S4` using `hskew q (ρ (st a) (P (f' u)))`. Rewrite using `[he, LinearMap.map_sub₂]`. Take the linear combination `S1 - F2 + S3 - F7 - S4 - F3 - S2 + F5 - h4`.

Rewrite using `[hg, hZP z hz, sub_self, hT0, map_zero, sub_zero, add_zero]`. Conclude with `hmemG _ (hf'.2.1 z hz)`. Establish `ex : φ (g x) y = φ (P (f' (P x))) y + φ (T (x - P x) - P (T (x - P x))) y`. Rewrite using `[hg, map_add, LinearMap.add_apply]`. Establish `ey : φ x (g y) = φ x (P (f' (P y))) + φ x (T (y - P y) - P (T (y - P y)))`.

Rewrite using `[hg, map_add]`. Establish `K1` using `L1 (f' (P x)) y`. Establish `K2` using `L2 (T (x - P x)) y`. Establish `K3` using `L3 x (f' (P y))`. Establish `K4` using `L4 x (T (y - P y))`.

Establish `K5` using `hT (P x) (y - P y)`. Establish `K6` using `hT (P y) (x - P x)`. Rewrite `K5`, `K6` using `[hPP]`. Establish `K7` using `hskew (T (x - P x)) (P y)`. Establish `K8` using `hskew (x - P x) (P (f' (P y)))`.

Take the linear combination `ex + ey + K1 + K2 + K3 + K4 + K5 + K7 - K6 + K8`. Rewrite using `[hconj, hg, hPP, sub_self, hT0, map_zero, sub_zero, add_zero, hPP]`. Establish `hu : x - P x ∈ G` using `hQG x`. Establish `hp : P (f' (x - P x)) ∈ G` using `hwP G _ (by`. Use `hf'.1 w (x - P x) hu` as an intermediate fact.

Rewrite using `[← hAdef, hQA, map_smul] at this)` and apply the resulting hypothesis. Establish `hq1` using `hQG (f' (x - P x))`. Establish `hq2` using `hQG (f' (P x))`. Establish `e1 : f' x = f' (P x) + f' (x - P x)` using `by rw [← map_add, add_sub_cancel]`. Establish `e : P (f' (P x)) - f' x = -(f' (P x) - P (f' (P x))) - (P (f' (x - P x)) + (f' (x - P x) - P (f' (x - P x))))` using `by rw [e1]; abel`.

Rewrite using `[e]`. Conclude with `G.sub_mem (G.neg_mem hq2) (G.add_mem hp hq1)`. Use `set p := ksSub ρ φ Fil Z with hp`. Establish `hmap : p.map (cls G ∘ₗ conj) = (ksSub ρ 0 G Z).map (cls G)`. Use extensionality with `m`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨conj g, hi g hg, rfl⟩`. Introduce and unpack `⟨f', hf', rfl⟩`. Take `⟨g, hg, hgf⟩` from `hiii f' hf'`.

Conclude with `⟨g, hg, (cls_eq_iff (Fil := G) _ _).2 hgf⟩`. Establish `hkerEq : LinearMap.ker (cls Fil ∘ₗ p.subtype) = LinearMap.ker ((cls G ∘ₗ conj) ∘ₗ p.subtype)`. Use extensionality with `⟨g, hg⟩`. Simplify using `only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]`. Establish `e1 : cls Fil g = 0 ↔ ∀ x ∈ Fil, g x ∈ Fil`.

Rewrite using `[← (cls Fil).map_zero, cls_eq_iff]`. Simplify using the standard rewrite rules. Establish `e2 : cls G (conj g) = 0 ↔ ∀ x ∈ G, conj g x ∈ G`. Rewrite using `[← (cls G).map_zero, cls_eq_iff]`. Simplify using the standard rewrite rules.

Rewrite using `[e1, e2]`. Conclude with `hker g hg`. Establish `h1` using `finrank_map_add_ker p (cls Fil)`. Establish `h2` using `finrank_map_add_ker p (cls G ∘ₗ conj)`. Rewrite `h1` using `[hkerEq]`.

Rewrite `h2` using `[hmap]`. Establish `hfin : finrank k (p.map (cls Fil)) = finrank k ((ksSub ρ 0 G Z).map (cls G))` using `by omega`. Establish `hd'` using `KSDim.unique hd (ksDim_finrank ρ 0 G Z)`. Use `ksDim_finrank ρ φ Fil Z` as an intermediate fact. Rewrite `this` using `[← hp, hfin, ← hd']`. Then use the resulting hypothesis.
-/
theorem ksDim_of_eigen_reduce : ∀ (k : Type) (H : Type 1) (O : Type) [Field k] [AddCommGroup H] [Module k H] [FiniteDimensional k H] [Ring O] (ρ : O →+* Module.End k H) (st : O → O) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (w : O) (r r' : k) (d : ℕ), Function.Surjective st → (∀ b x y, φ (ρ b x) y = φ x (ρ (st b) y)) → (∀ x y, φ x y = -φ y x) → (∀ x, (∀ y, φ x y = 0) → x = 0) → (∀ x ∈ Fil, ∀ y ∈ Fil, φ x y = 0) → 2 * Module.finrank k Fil = Module.finrank k H → (∀ a, ∀ x ∈ Fil, ρ a x ∈ Fil) → (∀ a, ρ w * ρ a = ρ a * ρ w) → (ρ w - r • 1) * (ρ w - r' • 1) = 0 → r ≠ r' → (∀ x y, φ (ρ w x) y = φ x ((r + r') • y - ρ w y)) → Z ≤ LinearMap.range (ρ w - r' • 1) → KSDim ρ 0 (Fil ⊔ LinearMap.range (ρ w - r • 1)) Z d → KSDim ρ φ Fil Z d := by
  intro k H O _ _ _ _ _ ρ st φ Fil Z w r r' d hst hadj hskew hnd hiso hdim hstab hcomm hA hr hφw hZ hd
  set A := ρ w with hAdef
  have hA2 : ∀ x, A (A x) = (r + r') • A x - (r * r') • x := by
    intro x
    have h := LinearMap.congr_fun hA x
    simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, map_smul, LinearMap.zero_apply] at h
    linear_combination (norm := module) h
  have hrr : r - r' ≠ 0 := sub_ne_zero.2 hr
  set c := (r - r')⁻¹ with hc
  have hc1 : c * (r - r') = 1 := inv_mul_cancel₀ hrr
  let P : Module.End k H := c • (A - r' • 1)
  have hPx : ∀ x, P x = c • (A x - r' • x) := fun x => by simp [P]
  have hPA : ∀ x, A (P x) = r • P x := by
    intro x; rw [hPx, map_smul, map_sub, map_smul, hA2]
    linear_combination (norm := module) (0:k) • x
  have hPfix : ∀ x, A x = r • x → P x = x := by
    intro x hx; rw [hPx, hx]
    linear_combination (norm := module) hc1 • x
  have hPkill : ∀ x, A x = r' • x → P x = 0 := by
    intro x hx; rw [hPx, hx]; simp
  have hQA : ∀ x, A (x - P x) = r' • (x - P x) := by
    intro x; rw [map_sub, hPA]
    have : A x - r' • x = (r - r') • P x := by rw [hPx, smul_smul, mul_comm, hc1, one_smul]
    linear_combination (norm := module) this
  have hPP : ∀ x, P (P x) = P x := fun x => hPfix _ (hPA x)
  have hPQ : ∀ x, P (x - P x) = 0 := fun x => hPkill _ (hQA x)

  have hAρ : ∀ a x, A (ρ a x) = ρ a (A x) := fun a x => LinearMap.congr_fun (hcomm a) x
  have hPρ : ∀ a x, P (ρ a x) = ρ a (P x) := by
    intro a x; rw [hPx, hPx, hAρ, map_smul, map_sub, map_smul]
  have hPFil : ∀ x ∈ Fil, P x ∈ Fil := fun x hx => by
    rw [hPx]; exact Fil.smul_mem _ (Fil.sub_mem (hstab w x hx) (Fil.smul_mem _ hx))
  have hQFil : ∀ x ∈ Fil, x - P x ∈ Fil := fun x hx => Fil.sub_mem hx (hPFil x hx)
  have hφeig : ∀ (s t : k), s ≠ t → s + t = r + r' → ∀ u v, A u = s • u → A v = s • v → φ u v = 0 := by
    intro s t hst' hsum u v hu hv
    have h := hφw u v
    rw [hu, hv] at h
    simp only [map_smul, LinearMap.smul_apply, map_sub, LinearMap.sub_apply, smul_eq_mul] at h
    have h2 : (s - t) * φ u v = 0 := by linear_combination h - (φ u v) * hsum
    exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hst')
  have hφPP : ∀ x y, φ (P x) (P y) = 0 := fun x y => hφeig r r' hr rfl _ _ (hPA x) (hPA y)
  have hφQQ : ∀ x y, φ (x - P x) (y - P y) = 0 := fun x y =>
    hφeig r' r (Ne.symm hr) (add_comm _ _) _ _ (hQA x) (hQA y)
  have hφdec : ∀ a b, φ a b = φ (P a) (b - P b) + φ (a - P a) (P b) := by
    intro a b
    have e : φ a b = φ (P a + (a - P a)) (P b + (b - P b)) := by simp
    rw [e]
    simp only [map_add, LinearMap.add_apply, hφPP, hφQQ]
    ring
  have hnd' : φ.Nondegenerate := ⟨hnd, fun y h => hnd y (fun x => by rw [hskew, h x, neg_zero])⟩
  have hperp : ∀ v, (∀ y ∈ Fil, φ v y = 0) → v ∈ Fil := by
    have hle : Fil ≤ φ.orthogonal Fil := by
      intro x hx
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro y hy
      exact hiso y hy x hx
    have hdim2 := LinearMap.BilinForm.finrank_orthogonal hnd' Fil
    have heq : Fil = φ.orthogonal Fil := Submodule.eq_of_le_of_finrank_le hle (by omega)
    intro v hv
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    change φ y v = 0
    rw [hskew, hv y hy, neg_zero]

  have hAP : ∀ v, A v - r' • v = (r - r') • P v := fun v => by
    rw [hPx, smul_smul, mul_comm, hc1, one_smul]
  have hPAc : ∀ x, P (A x) = A (P x) := fun x => by rw [hPx, hPx, map_smul, map_sub, map_smul]
  set G := Fil ⊔ LinearMap.range (A - r • 1) with hG
  have hrangeP : ∀ y ∈ LinearMap.range (A - r • 1), P y = 0 := by
    rintro _ ⟨z, rfl⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hPAc, hPA, sub_self]
  have hFilG : Fil ≤ G := le_sup_left
  have hmemG : ∀ x ∈ G, P x ∈ Fil := by
    intro x hx
    obtain ⟨f, hf, y, hy, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add, hrangeP y hy, add_zero]
    exact hPFil f hf
  have hQG : ∀ x, x - P x ∈ G := by
    intro x
    apply Submodule.mem_sup_right
    refine ⟨(-c) • x, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    have h := hAP x
    linear_combination (norm := module) (-c) • h - hc1 • P x + hc1 • x
  have hZP : ∀ z ∈ Z, P z = z := by
    intro z hz
    obtain ⟨y, rfl⟩ := hZ hz
    apply hPfix
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hA2]
    module
  have hwQ : ∀ (F : Submodule k H) v, r • v - A v ∈ F → v - P v ∈ F := by
    intro F v hv
    have e : v - P v = c • (r • v - A v) := by
      have h := hAP v
      linear_combination (norm := module) c • h - hc1 • v + hc1 • P v
    rw [e]; exact F.smul_mem _ hv
  have hwP : ∀ (F : Submodule k H) v, r' • v - A v ∈ F → P v ∈ F := by
    intro F v hv
    have e : P v = (-c) • (r' • v - A v) := by
      have h := hAP v
      linear_combination (norm := module) (-c) • h - hc1 • P v
    rw [e]; exact F.smul_mem _ hv
  have L1 : ∀ v y, φ (P v) y = φ (P v) (y - P y) := fun v y => by
    rw [hφdec (P v) y]; simp [hPP]
  have L2 : ∀ v y, φ (v - P v) y = φ v (P y) := fun v y => by
    rw [hφdec (v - P v) y, hφdec v (P y)]; simp [hPP, hPQ]
  have L3 : ∀ x v, φ x (P v) = φ (x - P x) (P v) := fun x v => by
    rw [hφdec x (P v)]; simp [hPP]
  have L4 : ∀ x v, φ x (v - P v) = φ (P x) v := fun x v => by
    rw [hφdec x (v - P v), hφdec (P x) v]; simp [hPP, hPQ]
  have hQcrit : ∀ v, (∀ y ∈ Fil, φ v (P y) = 0) → v - P v ∈ Fil := by
    intro v hv
    apply hperp
    intro y hy
    rw [L2]; exact hv y hy

  let conj : (H →ₗ[k] H) →ₗ[k] (H →ₗ[k] H) :=
    { toFun := fun g => P ∘ₗ g ∘ₗ P
      map_add' := fun f g => by ext; simp
      map_smul' := fun a f => by ext; simp }
  have hconj : ∀ g x, conj g x = P (g (P x)) := fun _ _ => rfl
  have hi : ∀ g, IsKS ρ φ Fil Z g → IsKS ρ 0 G Z (conj g) := by
    intro g hg
    refine ⟨fun a x hx => ?_, fun x hx => ?_, fun x _ y _ => by simp⟩
    · rw [hconj, hconj, hPρ a x, ← hPρ a (g (P x)), ← map_sub]
      exact hFilG (hPFil _ (hg.1 a _ (hmemG x hx)))
    · rw [hconj, hZP x hx]; exact hFilG (hPFil _ (hg.2.1 x hx))
  have hker : ∀ g, IsKS ρ φ Fil Z g → ((∀ x ∈ Fil, g x ∈ Fil) ↔ (∀ x ∈ G, conj g x ∈ G)) := by
    intro g hg
    constructor
    · intro h x hx
      rw [hconj]; exact hFilG (hPFil _ (h _ (hmemG x hx)))
    · intro h
      have hPpart : ∀ u ∈ Fil, P (g (P u)) ∈ Fil := by
        intro u hu
        have := hmemG _ (h (P u) (hFilG (hPFil u hu)))
        rwa [hconj, hPP, hPP] at this
      have hgP : ∀ u ∈ Fil, g (P u) ∈ Fil := by
        intro u hu
        have hq : g (P u) - P (g (P u)) ∈ Fil := by
          apply hwQ
          have := hg.1 w (P u) (hPFil u hu)
          rwa [← hAdef, hPA, map_smul] at this
        have := Fil.add_mem hq (hPpart u hu)
        rwa [sub_add_cancel] at this
      intro x hx
      have hu : x - P x ∈ Fil := hQFil x hx
      have hp : P (g (x - P x)) ∈ Fil := by
        apply hwP
        have := hg.1 w (x - P x) hu
        rwa [← hAdef, hQA, map_smul] at this
      have hq : g (x - P x) - P (g (x - P x)) ∈ Fil := by
        apply hQcrit
        intro y hy
        have h1 := hg.2.2 (x - P x) hu (P y) (hPFil y hy)
        have h2 := hiso (x - P x) hu _ (hgP y hy)
        linear_combination h1 - h2
      have e : g x = g (P x) + (P (g (x - P x)) + (g (x - P x) - P (g (x - P x)))) := by
        rw [add_sub_cancel, ← map_add, add_sub_cancel]
      rw [e]
      exact Fil.add_mem (hgP x hx) (Fil.add_mem hp hq)

  have hiii : ∀ f', IsKS ρ 0 G Z f' → ∃ g, IsKS ρ φ Fil Z g ∧ ∀ x ∈ G, conj g x - f' x ∈ G := by
    intro f' hf'
    have hinj : Function.Injective φ.flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      apply hnd v
      intro u
      rw [hskew]
      have : φ u v = 0 := LinearMap.congr_fun hv u
      rw [this, neg_zero]
    have hsurj : Function.Surjective φ.flip :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq).symm).1 hinj
    obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective φ.flip (LinearMap.range_eq_top.2 hsurj)
    let L : H →ₗ[k] H := P ∘ₗ f' ∘ₗ P
    let T : H →ₗ[k] H := s ∘ₗ (-(L.dualMap ∘ₗ φ.flip))
    have hT : ∀ u v, φ u (T v) = -φ (P (f' (P u))) v := by
      intro u v
      have := LinearMap.congr_fun (LinearMap.congr_fun hs (-(L.dualMap ∘ₗ φ.flip) v)) u
      simpa [T, L] using this
    let g : H →ₗ[k] H := L + (1 - P) ∘ₗ T ∘ₗ (1 - P)
    have hg : ∀ x, g x = P (f' (P x)) + (T (x - P x) - P (T (x - P x))) := fun x => by
      simp [g, L]
    have hT0 : T 0 = 0 := map_zero T
    refine ⟨g, ⟨fun a x hx => ?_, fun z hz => ?_, fun x _ y _ => ?_⟩, fun x hx => ?_⟩
    · obtain ⟨q, hq⟩ : ∃ q, q = x - P x := ⟨_, rfl⟩
      obtain ⟨e, he⟩ : ∃ e, e = T (ρ a q) - ρ a (T q) := ⟨_, rfl⟩
      have hqF : q ∈ Fil := hq ▸ hQFil x hx
      have eq : g (ρ a x) - ρ a (g x) = P (f' (ρ a (P x)) - ρ a (f' (P x))) + (e - P e) := by
        have hq' : ρ a x - P (ρ a x) = ρ a q := by rw [hq, hPρ, ← map_sub]
        rw [hg, hg, hq', he, ← hq]
        simp only [hPρ, map_sub, map_add]
        abel
      rw [eq]
      refine Fil.add_mem (hmemG _ (hf'.1 a _ (hFilG (hPFil x hx)))) (hQcrit e fun y hy => ?_)
      set u := P y with hu
      set t := T q with ht
      have hm : P (f' (ρ (st a) u)) - ρ (st a) (P (f' u)) ∈ Fil := by
        rw [← hPρ (st a) (f' u), ← map_sub]; exact hmemG _ (hf'.1 (st a) u (hFilG (hPFil y hy)))
      have h4 := hiso _ hm q hqF
      rw [LinearMap.map_sub₂] at h4
      have F2 : φ u (T (ρ a q)) = -φ (P (f' u)) (ρ a q) := by rw [hT, hu, hPP]
      have F5 : φ (ρ (st a) u) t = -φ (P (f' (ρ (st a) u))) q := by rw [ht, hT, hu, hPρ, hPP]
      have F3 := hadj a t u
      have F7 := hadj a q (P (f' u))
      have S1 := hskew (T (ρ a q)) u
      have S2 := hskew t (ρ (st a) u)
      have S3 := hskew (P (f' u)) (ρ a q)
      have S4 := hskew q (ρ (st a) (P (f' u)))
      rw [he, LinearMap.map_sub₂]
      linear_combination S1 - F2 + S3 - F7 - S4 - F3 - S2 + F5 - h4
    · rw [hg, hZP z hz, sub_self, hT0, map_zero, sub_zero, add_zero]
      exact hmemG _ (hf'.2.1 z hz)
    · have ex : φ (g x) y = φ (P (f' (P x))) y + φ (T (x - P x) - P (T (x - P x))) y := by
        rw [hg, map_add, LinearMap.add_apply]
      have ey : φ x (g y) = φ x (P (f' (P y))) + φ x (T (y - P y) - P (T (y - P y))) := by
        rw [hg, map_add]
      have K1 := L1 (f' (P x)) y
      have K2 := L2 (T (x - P x)) y
      have K3 := L3 x (f' (P y))
      have K4 := L4 x (T (y - P y))
      have K5 := hT (P x) (y - P y)
      have K6 := hT (P y) (x - P x)
      rw [hPP] at K5 K6
      have K7 := hskew (T (x - P x)) (P y)
      have K8 := hskew (x - P x) (P (f' (P y)))
      linear_combination ex + ey + K1 + K2 + K3 + K4 + K5 + K7 - K6 + K8
    · rw [hconj, hg, hPP, sub_self, hT0, map_zero, sub_zero, add_zero, hPP]
      have hu : x - P x ∈ G := hQG x
      have hp : P (f' (x - P x)) ∈ G := hwP G _ (by
        have := hf'.1 w (x - P x) hu
        rwa [← hAdef, hQA, map_smul] at this)
      have hq1 := hQG (f' (x - P x))
      have hq2 := hQG (f' (P x))
      have e1 : f' x = f' (P x) + f' (x - P x) := by rw [← map_add, add_sub_cancel]
      have e : P (f' (P x)) - f' x = -(f' (P x) - P (f' (P x))) -
          (P (f' (x - P x)) + (f' (x - P x) - P (f' (x - P x)))) := by rw [e1]; abel
      rw [e]
      exact G.sub_mem (G.neg_mem hq2) (G.add_mem hp hq1)

  set p := ksSub ρ φ Fil Z with hp
  have hmap : p.map (cls G ∘ₗ conj) = (ksSub ρ 0 G Z).map (cls G) := by
    ext m
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨conj g, hi g hg, rfl⟩
    · rintro ⟨f', hf', rfl⟩
      obtain ⟨g, hg, hgf⟩ := hiii f' hf'
      exact ⟨g, hg, (cls_eq_iff (Fil := G) _ _).2 hgf⟩
  have hkerEq : LinearMap.ker (cls Fil ∘ₗ p.subtype) = LinearMap.ker ((cls G ∘ₗ conj) ∘ₗ p.subtype) := by
    ext ⟨g, hg⟩
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]
    have e1 : cls Fil g = 0 ↔ ∀ x ∈ Fil, g x ∈ Fil := by
      rw [← (cls Fil).map_zero, cls_eq_iff]; simp
    have e2 : cls G (conj g) = 0 ↔ ∀ x ∈ G, conj g x ∈ G := by
      rw [← (cls G).map_zero, cls_eq_iff]; simp
    rw [e1, e2]
    exact hker g hg
  have h1 := finrank_map_add_ker p (cls Fil)
  have h2 := finrank_map_add_ker p (cls G ∘ₗ conj)
  rw [hkerEq] at h1
  rw [hmap] at h2
  have hfin : finrank k (p.map (cls Fil)) = finrank k ((ksSub ρ 0 G Z).map (cls G)) := by omega
  have hd' := KSDim.unique hd (ksDim_finrank ρ 0 G Z)
  have := ksDim_finrank ρ φ Fil Z
  rwa [← hp, hfin, ← hd'] at this

end GlobalTheory.UPel.Sm.KSCount
