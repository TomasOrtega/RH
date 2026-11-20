import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FreeProf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.GenExt

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ L G0 T hT`. Set `H0 : Subgroup G0.Γ` to `(T.H : Subgroup G0.Γ)`. Establish `hH0open : IsOpen (H0 : Set G0.Γ)` using `T.H.isOpen`. Choose the witnesses or unpack the hypotheses as in `⟨n, e, he⟩ : ∃ n : ℕ, ∃ e : Fin n → G0.Γ ⧸ H0, Function.Surjective e := by`. Take `⟨n, ⟨eq⟩⟩` from `Finite.exists_equiv_fin (G0.Γ ⧸ H0)`.

Conclude with `⟨n, eq.symm, eq.symm.surjective⟩`. Set `lift : G0.Γ ⧸ H0 → G0.Γ` to `Function.surjInv QuotientGroup.mk_surjective`. Establish `hlift : ∀ y, (QuotientGroup.mk (lift y) : G0.Γ ⧸ H0) = y` using `Function.surjInv_eq QuotientGroup.mk_surjective`. Set `yc : Fin (n + 1) → G0.Γ` to `Fin.cons G0.c (fun i => lift (e i))`. Set `γ : Fin (n + 1) → G0.Γ ⧸ H0` to `fun i => QuotientGroup.mk (yc i)`.

Establish `hγ : Function.Surjective γ`. Introduce `y`. Take `⟨i, rfl⟩` from `he y`. Conclude with `⟨i.succ, by simp [γ, yc, hlift]⟩`. Take `⟨P, iG, iT, iTG, iC, iTD, x, hx, hfree⟩` from `exists_free_profinite (n + 1 + T.hb)`.

Take `⟨f0, hf0c, hf0x⟩` from `hfree G0.Γ (Fin.append yc (fun _ => 1))`. Set `π0 : P →* G0.Γ ⧸ H0` to `(QuotientGroup.mk' H0).comp f0`. Establish `hπ0ker : IsOpen (π0.ker : Set P)`. Establish `: (π0.ker : Set P) = f0 ⁻¹' (H0 : Set G0.Γ)`. Use extensionality with `g`.

Simplify using `[π0, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]`. Rewrite using `[this]`. Conclude with `hH0open.preimage hf0c`. Establish `hcast : ∀ i : Fin (n + 1), π0 (x (Fin.castAdd T.hb i)) = γ i`. Introduce `i`.

Simplify using `[π0, γ, hf0x, Fin.append_left]`. Establish `hnat : ∀ i : Fin T.hb, π0 (x (Fin.natAdd (n + 1) i)) = 1`. Introduce `i`. Simplify using `[π0, hf0x, Fin.append_right]`. Establish `key : ∀ N : ℕ, ∃ f : P →* (T.GN N).Γ, Continuous f ∧ Function.Surjective f ∧ ((QuotientGroup.mk' H0).comp (T.h N).p).comp f = π0 ∧ f (x (Fin.castAdd T.hb 0)) = (T.GN N).c`.

Introduce `N`. Set `p` to `(T.h N).p`. Set `q : (T.GN N).Γ →* G0.Γ ⧸ H0` to `(QuotientGroup.mk' H0).comp p`. Set `HN : Subgroup (T.GN N).Γ` to `H0.comap p`. Use `haveI : HN.Normal := Subgroup.Normal.comap inferInstance p`.

Establish `hqker : q.ker = HN`. Use extensionality with `g`. Simplify using `[q, HN, p, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]`. Establish `hHNopen : IsOpen (HN : Set (T.GN N).Γ)` using `hH0open.preimage (T.h N).cont`. Establish `hqopen : IsOpen (q.ker : Set (T.GN N).Γ)` using `by rw [hqker]; exact hHNopen`.

Set `g : Fin (n + 1) → (T.GN N).Γ` to `Fin.cons (T.GN N).c (fun i => Function.surjInv (T.h N).surj (yc i.succ))`. Establish `hg : ∀ i, q (g i) = γ i`. Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `[q, g, γ, yc, p, (T.h N).c]`.

Simplify using `[q, g, γ, p, Function.surjInv_eq (T.h N).surj]`. Establish `hz : ∃ z : Fin T.hb → ↥q.ker, TopGen (Set.range z)`. Rewrite using `[hqker]`. Establish `hPL` using `hT.2 N`. Establish `hfin` using `T.finN N`.

Conclude with `(pl_gen l (T.GN N).Γ HN hHNopen hPL hfin.1).2 T.hb hfin.2`. Take `⟨f, hfc, hfs, hfq, hfx⟩` from `exists_surj_over_finite P (G0.Γ ⧸ H0) (n + 1) T.hb x γ π0 hx hfree hγ hπ0ker hcast hnat (T.GN N).Γ q hqopen g hg hz`. Conclude with `⟨f, hfc, hfs, hfq, by rw [hfx 0]; simp [g]⟩`. Use `choose F hFc hFs hFq hFx using key`. Use `⟨P, iG, iT, iTG, iC, iTD, F, x (Fin.castAdd T.hb 0), ⟨Set.range x, Set.finite_range x, hx⟩, fun N => ⟨hFc N, hFs N, hFx N⟩, ?_⟩` and prove the remaining obligations.

Introduce `N N' g`. Establish `h1` using `congrArg (fun φ => φ g) (hFq N)`. Establish `h2` using `congrArg (fun φ => φ g) (hFq N')`. Simplify using `only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1 h2`. Establish `h3 : (QuotientGroup.mk ((T.h N).p (F N g)) : G0.Γ ⧸ H0) = QuotientGroup.mk ((T.h N').p (F N' g))`.

Rewrite using `[h1, h2]`. Rewrite `h3` using `[QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]`. Conclude with `h3`.
-/
theorem UpperTheory.V.Pa.sys_cover :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0), T.ProL → ∃ (Ph : Type) (_ : Group Ph) (_ : TopologicalSpace Ph) (_ : IsTopologicalGroup Ph) (_ : CompactSpace Ph) (_ : TotallyDisconnectedSpace Ph) (π : ∀ N, Ph →* (T.GN N).Γ) (ct : Ph), TopFG Ph ∧ (∀ N, Continuous (π N) ∧ Function.Surjective (π N) ∧ π N ct = (T.GN N).c) ∧ ∀ N N' g, (T.h N).p (π N g) * ((T.h N').p (π N' g))⁻¹ ∈ T.H := by
  intro l _ L G0 T hT
  classical
  let H0 : Subgroup G0.Γ := (T.H : Subgroup G0.Γ)
  have hH0open : IsOpen (H0 : Set G0.Γ) := T.H.isOpen
  obtain ⟨n, e, he⟩ : ∃ n : ℕ, ∃ e : Fin n → G0.Γ ⧸ H0, Function.Surjective e := by
    obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin (G0.Γ ⧸ H0)
    exact ⟨n, eq.symm, eq.symm.surjective⟩
  let lift : G0.Γ ⧸ H0 → G0.Γ := Function.surjInv QuotientGroup.mk_surjective
  have hlift : ∀ y, (QuotientGroup.mk (lift y) : G0.Γ ⧸ H0) = y :=
    Function.surjInv_eq QuotientGroup.mk_surjective
  let yc : Fin (n + 1) → G0.Γ := Fin.cons G0.c (fun i => lift (e i))
  let γ : Fin (n + 1) → G0.Γ ⧸ H0 := fun i => QuotientGroup.mk (yc i)
  have hγ : Function.Surjective γ := by
    intro y
    obtain ⟨i, rfl⟩ := he y
    exact ⟨i.succ, by simp [γ, yc, hlift]⟩
  obtain ⟨P, iG, iT, iTG, iC, iTD, x, hx, hfree⟩ := exists_free_profinite (n + 1 + T.hb)
  obtain ⟨f0, hf0c, hf0x⟩ := hfree G0.Γ (Fin.append yc (fun _ => 1))
  let π0 : P →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp f0
  have hπ0ker : IsOpen (π0.ker : Set P) := by
    have : (π0.ker : Set P) = f0 ⁻¹' (H0 : Set G0.Γ) := by
      ext g
      simp [π0, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    rw [this]
    exact hH0open.preimage hf0c
  have hcast : ∀ i : Fin (n + 1), π0 (x (Fin.castAdd T.hb i)) = γ i := by
    intro i
    simp [π0, γ, hf0x, Fin.append_left]
  have hnat : ∀ i : Fin T.hb, π0 (x (Fin.natAdd (n + 1) i)) = 1 := by
    intro i
    simp [π0, hf0x, Fin.append_right]
  have key : ∀ N : ℕ, ∃ f : P →* (T.GN N).Γ, Continuous f ∧ Function.Surjective f ∧
      ((QuotientGroup.mk' H0).comp (T.h N).p).comp f = π0 ∧
      f (x (Fin.castAdd T.hb 0)) = (T.GN N).c := by
    intro N
    let p := (T.h N).p
    let q : (T.GN N).Γ →* G0.Γ ⧸ H0 := (QuotientGroup.mk' H0).comp p
    let HN : Subgroup (T.GN N).Γ := H0.comap p
    haveI : HN.Normal := Subgroup.Normal.comap inferInstance p
    have hqker : q.ker = HN := by
      ext g
      simp [q, HN, p, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
    have hHNopen : IsOpen (HN : Set (T.GN N).Γ) := hH0open.preimage (T.h N).cont
    have hqopen : IsOpen (q.ker : Set (T.GN N).Γ) := by rw [hqker]; exact hHNopen
    let g : Fin (n + 1) → (T.GN N).Γ :=
      Fin.cons (T.GN N).c (fun i => Function.surjInv (T.h N).surj (yc i.succ))
    have hg : ∀ i, q (g i) = γ i := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [q, g, γ, yc, p, (T.h N).c]
      · simp [q, g, γ, p, Function.surjInv_eq (T.h N).surj]
    have hz : ∃ z : Fin T.hb → ↥q.ker, TopGen (Set.range z) := by
      rw [hqker]
      have hPL := hT.2 N
      have hfin := T.finN N
      exact (pl_gen l (T.GN N).Γ HN hHNopen hPL hfin.1).2 T.hb hfin.2
    obtain ⟨f, hfc, hfs, hfq, hfx⟩ :=
      exists_surj_over_finite P (G0.Γ ⧸ H0) (n + 1) T.hb x γ π0 hx hfree hγ hπ0ker hcast hnat
        (T.GN N).Γ q hqopen g hg hz
    exact ⟨f, hfc, hfs, hfq, by rw [hfx 0]; simp [g]⟩
  choose F hFc hFs hFq hFx using key
  refine ⟨P, iG, iT, iTG, iC, iTD, F, x (Fin.castAdd T.hb 0), ⟨Set.range x, Set.finite_range x, hx⟩,
    fun N => ⟨hFc N, hFs N, hFx N⟩, ?_⟩
  intro N N' g
  have h1 := congrArg (fun φ => φ g) (hFq N)
  have h2 := congrArg (fun φ => φ g) (hFq N')
  simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply] at h1 h2
  have h3 : (QuotientGroup.mk ((T.h N).p (F N g)) : G0.Γ ⧸ H0) = QuotientGroup.mk ((T.h N').p (F N' g)) := by
    rw [h1, h2]
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h3
  exact h3
