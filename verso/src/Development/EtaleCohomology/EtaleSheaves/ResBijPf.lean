import Development.EtaleCohomology.EtaleSheaves.HZeroPf
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ResBijPf

def TwSec : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), (∀ (U : Scheme.{0}) (y : Sec (tw q i) U), Loc U fun V g => Sec.res g y = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g y = c • twGen i ζ) ∧ (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U), Loc U fun V g => ∃ c : ℕ, Sec.res g y = c • twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) [Nonempty U] (ζ : Prim q Γ(U, ⊤)) (c : ℕ), c • twGen i ζ = 0 → q ∣ c) ∧ (∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)), Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom)) ∧ (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → twGen i ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • twGen i ζ) ∧ ∀ (M : Shv (ZMod q)) (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec M U), (∀ (V U : Scheme.{0}) (g : V ⟶ U) ζ, Sec.res g (e U ζ) = e V (ζ.map g.appTop.hom)) → (∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ), ξ.1 = ζ.1 ^ (a : ZMod q).val → e U ξ = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • e U ζ) → ∃! φ : tw q i ⟶ M, ∀ U ζ, Sec.map φ (twGen i ζ) = e U ζ

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

/- English proof (translation)
The claim follows from `map_nsmul _ n x`.
-/
theorem res_nsmul' {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ n x

/- English proof (translation)
Establish `h1` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)`. Conclude with `(h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)`.
-/
theorem sep' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology U)
    (y z : Sec F U) (h : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec.res g y = Sec.res g z) : y = z := by
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => h V g hg)

/- English proof (translation)
The claim follows from `sep' ⊥ (Scheme.bot_mem_grothendieckTopology U) y z (fun _ _ h => h.elim)`.
-/
theorem sec_empty {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} [IsEmpty U] (y z : Sec F U) : y = z :=
  sep' ⊥ (Scheme.bot_mem_grothendieckTopology U) y z (fun _ _ h => h.elim)

variable {q : ℕ} {i : ℤ}

/- English proof (translation)
Establish `hq : q • G = 0`. Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0` using `by ext; simp`. Rewrite using `[this, zero_smul]`. Use `conv_lhs => rw [← Nat.mod_add_div a q]`.

Rewrite using `[add_smul, mul_comm, mul_smul, hq, smul_zero, add_zero]`.
-/
theorem smul_mod {U : Scheme.{0}} (G : Sec (tw q i) U) (a : ℕ) : a • G = (a % q) • G := by
  have hq : q • G = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
    have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by
      ext; simp
    rw [this, zero_smul]
  conv_lhs => rw [← Nat.mod_add_div a q]
  rw [add_smul, mul_comm, mul_smul, hq, smul_zero, add_zero]

/- English proof (translation)
Rewrite using `[smul_mod G a, smul_mod G b, (ZMod.natCast_eq_natCast_iff' a b q).1 h]`.
-/
theorem smul_eq_of_cast {U : Scheme.{0}} (G : Sec (tw q i) U) {a b : ℕ} (h : (a : ZMod q) = b) : a • G = b • G := by
  rw [smul_mod G a, smul_mod G b, (ZMod.natCast_eq_natCast_iff' a b q).1 h]

/- English proof (translation)
Rewrite using `[ZMod.natCast_eq_natCast_iff']`. Rewrite `h` using `[smul_mod _ a, smul_mod _ b]`. Establish `ha` using `Nat.mod_lt a (NeZero.pos q)`. Establish `hb` using `Nat.mod_lt b (NeZero.pos q)`. Establish `key : ∀ x y : ℕ, x < q → y < q → x ≤ y → x • twGen i ζ = y • twGen i ζ → x = y`.

Introduce `x y hx hy hxy he`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hxy`. Rewrite `he` using `[add_smul]`. Establish `hd : d • twGen i ζ = 0`. Use `congrArg (fun t => t - x • twGen i ζ) he` as an intermediate fact.

Simplify using `using this.symm`. Use `(hT q i).2.2.1 U ζ d hd` as an intermediate fact. Establish `: d = 0` using `Nat.eq_zero_of_dvd_of_lt this (by omega)`. Use linear arithmetic over natural numbers and integers. Break down `le_total (a % q) (b % q) with hab | hab` into its components or cases.

Conclude with `key _ _ ha hb hab h`. Conclude with `(key _ _ hb ha hab h.symm).symm`.
-/
theorem cast_of_smul_eq (hT : TwSec) [NeZero q] {U : Scheme.{0}} [Nonempty U] (ζ : Prim q Γ(U, ⊤)) {a b : ℕ}
    (h : a • twGen i ζ = b • twGen i ζ) : (a : ZMod q) = b := by
  rw [ZMod.natCast_eq_natCast_iff']
  rw [smul_mod _ a, smul_mod _ b] at h
  have ha := Nat.mod_lt a (NeZero.pos q)
  have hb := Nat.mod_lt b (NeZero.pos q)
  have key : ∀ x y : ℕ, x < q → y < q → x ≤ y → x • twGen i ζ = y • twGen i ζ → x = y := by
    intro x y hx hy hxy he
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hxy
    rw [add_smul] at he
    have hd : d • twGen i ζ = 0 := by
      have := congrArg (fun t => t - x • twGen i ζ) he
      simpa using this.symm
    have := (hT q i).2.2.1 U ζ d hd
    have : d = 0 := Nat.eq_zero_of_dvd_of_lt this (by omega)
    omega
  rcases le_total (a % q) (b % q) with hab | hab
  · exact key _ _ ha hb hab h
  · exact (key _ _ hb ha hab h.symm).symm

end LateralTheory.E.ResBijPf

namespace LateralTheory.E.ResBijPf
variable {q : ℕ} {i : ℤ}

/- English proof (translation)
Take `⟨S, hS, hSP⟩` from `(hT q i).2.1 U ζ s`. Take `⟨𝒰, hle⟩` from `Scheme.exists_cover_of_mem_grothendieckTopology hS`. Establish `hcov` using `(Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀`. Establish `hgen : ∀ {V : Scheme.{0}} (g : V ⟶ U) (n : ℕ), n • twGen i (ζ.map g.appTop.hom) = Sec.res g (n • twGen i ζ)`. Introduce `V g n`.

Rewrite using `[res_nsmul', (hT q i).2.2.2.1]`. Establish `hc : ∀ j, ∃ c : ℕ, Sec.res (𝒰.f j) s = Sec.res (𝒰.f j) (c • twGen i ζ)`. Introduce `j`. Take `⟨c, hc⟩` from `hSP _ _ (hle _ (𝒰.f j) (Presieve.ofArrows.mk j))`. Conclude with `⟨c, hc.trans (hgen _ _)⟩`.

Use `choose c hc using hc`. Establish `compat : ∀ j j' (x : 𝒰.X j) (x' : 𝒰.X j'), 𝒰.f j x = 𝒰.f j' x' → (c j : ZMod q) = c j'`. Introduce `j j' x x' hx`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback x x' hx`. Establish `: Nonempty ↑(pullback (𝒰.f j) (𝒰.f j') : Scheme.{0})` using `⟨z⟩`.

Establish `e1 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s = Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j • twGen i ζ)`. Rewrite using `[res_comp', hc j, ← res_comp']`. Establish `e2 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s = Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j' • twGen i ζ)`. Rewrite using `[pullback.condition, res_comp', hc j', ← res_comp']`. Rewrite `e1`, `e2` using `[← hgen]`.

Conclude with `cast_of_smul_eq hT _ (e1.symm.trans e2)`. Establish `hopen : ∀ j, IsOpen (Set.range (𝒰.f j))`. Introduce `j`. Use `hcov.2 j` as an intermediate fact. Conclude with `(𝒰.f j).isOpenMap.isOpen_range`.

Take `⟨x0⟩` from `(inferInstance : Nonempty U)`. Take `⟨j0, y0, hy0⟩` from `hcov.1 x0`. Establish `claim : ∀ j (y : 𝒰.X j), (c j : ZMod q) = c j0`. Introduce `j y`. Assume the negation of the conclusion as `hne`.

Establish `hpc` using `(isPreconnected_univ (α := U)) (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) = c j0), Set.range (𝒰.f j)) (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) ≠ c j0), Set.range (𝒰.f j)) (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j) (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j) (by`. Introduce `x _`. Take `⟨j', y', hy'⟩` from `hcov.1 x`. Distinguish the cases in `h : (c j' : ZMod q) = c j0`. Conclude with `Or.inl (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩)`.

Conclude with `Or.inr (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩))`. Use the proof step `⟨x0, trivial, Set.mem_iUnion₂.2 ⟨j0, rfl, y0, hy0⟩⟩`. Use the proof step `⟨𝒰.f j y, trivial, Set.mem_iUnion₂.2 ⟨j, hne, y, rfl⟩⟩`. Take `⟨x, -, hA, hB⟩` from `hpc`. Take `⟨j1, h1, y1, hy1⟩` from `Set.mem_iUnion₂.1 hA`.

Take `⟨j2, h2, y2, hy2⟩` from `Set.mem_iUnion₂.1 hB`. Conclude with `h2 ((compat j2 j1 y2 y1 (hy2.trans hy1.symm)).trans h1)`. Use `⟨c j0, sep' _ (Scheme.Cover.mem_grothendieckTopology 𝒰) _ _ ?_⟩` and prove the remaining obligations. Introduce and unpack `V g ⟨W, h, g', hg', rfl⟩`. Consider the cases of `hg' with`.

Consider the case `mk j`. Rewrite using `[res_comp', res_comp', hc j]`. Use `congr 1`. Break down `isEmpty_or_nonempty (𝒰.X j) with he | ⟨⟨y⟩⟩` into its components or cases. Conclude with `sec_empty _ _`.

Rewrite using `[smul_eq_of_cast _ (claim j y)]`.
-/
theorem surj (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤))
    (s : Sec (tw q i) U) : ∃ k : ℕ, s = k • twGen i ζ := by
  obtain ⟨S, hS, hSP⟩ := (hT q i).2.1 U ζ s
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hS
  have hcov := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).1 𝒰.mem₀
  have hgen : ∀ {V : Scheme.{0}} (g : V ⟶ U) (n : ℕ),
      n • twGen i (ζ.map g.appTop.hom) = Sec.res g (n • twGen i ζ) := by
    intro V g n
    rw [res_nsmul', (hT q i).2.2.2.1]
  have hc : ∀ j, ∃ c : ℕ, Sec.res (𝒰.f j) s = Sec.res (𝒰.f j) (c • twGen i ζ) := by
    intro j
    obtain ⟨c, hc⟩ := hSP _ _ (hle _ (𝒰.f j) (Presieve.ofArrows.mk j))
    exact ⟨c, hc.trans (hgen _ _)⟩
  choose c hc using hc
  have compat : ∀ j j' (x : 𝒰.X j) (x' : 𝒰.X j'), 𝒰.f j x = 𝒰.f j' x' → (c j : ZMod q) = c j' := by
    intro j j' x x' hx
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x x' hx
    have : Nonempty ↑(pullback (𝒰.f j) (𝒰.f j') : Scheme.{0}) := ⟨z⟩
    have e1 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j • twGen i ζ) := by
      rw [res_comp', hc j, ← res_comp']
    have e2 : Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) s =
        Sec.res (pullback.fst (𝒰.f j) (𝒰.f j') ≫ 𝒰.f j) (c j' • twGen i ζ) := by
      rw [pullback.condition, res_comp', hc j', ← res_comp']
    rw [← hgen] at e1 e2
    exact cast_of_smul_eq hT _ (e1.symm.trans e2)
  have hopen : ∀ j, IsOpen (Set.range (𝒰.f j)) := by
    intro j
    have := hcov.2 j
    exact (𝒰.f j).isOpenMap.isOpen_range
  obtain ⟨x0⟩ := (inferInstance : Nonempty U)
  obtain ⟨j0, y0, hy0⟩ := hcov.1 x0
  have claim : ∀ j (y : 𝒰.X j), (c j : ZMod q) = c j0 := by
    intro j y
    by_contra hne
    have hpc := (isPreconnected_univ (α := U))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) = c j0), Set.range (𝒰.f j))
      (⋃ (j : 𝒰.I₀) (_ : (c j : ZMod q) ≠ c j0), Set.range (𝒰.f j))
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (isOpen_iUnion fun j => isOpen_iUnion fun _ => hopen j)
      (by
        intro x _
        obtain ⟨j', y', hy'⟩ := hcov.1 x
        by_cases h : (c j' : ZMod q) = c j0
        · exact Or.inl (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩)
        · exact Or.inr (Set.mem_iUnion₂.2 ⟨j', h, y', hy'⟩))
      ⟨x0, trivial, Set.mem_iUnion₂.2 ⟨j0, rfl, y0, hy0⟩⟩
      ⟨𝒰.f j y, trivial, Set.mem_iUnion₂.2 ⟨j, hne, y, rfl⟩⟩
    obtain ⟨x, -, hA, hB⟩ := hpc
    obtain ⟨j1, h1, y1, hy1⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j2, h2, y2, hy2⟩ := Set.mem_iUnion₂.1 hB
    exact h2 ((compat j2 j1 y2 y1 (hy2.trans hy1.symm)).trans h1)
  refine ⟨c j0, sep' _ (Scheme.Cover.mem_grothendieckTopology 𝒰) _ _ ?_⟩
  rintro V g ⟨W, h, g', hg', rfl⟩
  cases hg' with
  | mk j =>
    rw [res_comp', res_comp', hc j]
    congr 1
    rcases isEmpty_or_nonempty (𝒰.X j) with he | ⟨⟨y⟩⟩
    · exact sec_empty _ _
    · rw [smul_eq_of_cast _ (claim j y)]

/- English proof (translation)
Use `⟨fun k k' h => ?_, fun s => ?_⟩` and prove the remaining obligations. Use `cast_of_smul_eq hT ζ h` as an intermediate fact. Simplify using `using this`. Take `⟨n, rfl⟩` from `surj (i := i) hT ζ s`. Use `⟨(n : ZMod q), smul_eq_of_cast _ ?_⟩` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem gen_bij (hT : TwSec) [NeZero q] {U : Scheme.{0}} [ConnectedSpace U] (ζ : Prim q Γ(U, ⊤)) :
    Function.Bijective (fun k : ZMod q => k.val • twGen i ζ) := by
  refine ⟨fun k k' h => ?_, fun s => ?_⟩
  · have := cast_of_smul_eq hT ζ h
    simpa using this
  · obtain ⟨n, rfl⟩ := surj (i := i) hT ζ s
    refine ⟨(n : ZMod q), smul_eq_of_cast _ ?_⟩
    simp

/- English proof (translation)
Introduce `q i Y X f hY hX ⟨ζ⟩`. Establish `: NeZero q` using `⟨fun h0 => by`. Substitute `h0` using the available equality. Take `⟨x⟩` from `(inferInstance : Nonempty X)`. Establish `: Nonempty (⊤ : X.Opens)` using `⟨⟨x, trivial⟩⟩`.

Establish `h` using `ζ.2.1`. Simplify using `only [Nat.cast_zero, isUnit_zero_iff] at h`. Conclude with `zero_ne_one h⟩`. Establish `h1` using `gen_bij (i := i) hT ζ`. Establish `h2` using `gen_bij (i := i) hT (ζ.map f.appTop.hom)`.

Establish `e : (Sec.res (F` using `tw q i) f) ∘ (fun k : ZMod q => k.val • twGen i ζ) = fun k : ZMod q => k.val • twGen i (ζ.map f.appTop.hom) := by`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp]`. Rewrite using `[res_nsmul', (hT q i).2.2.2.1]`. Conclude with `(Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)`.
-/
theorem ResBij_of (hT : TwSec) : LateralTheory.E.HZeroPf.ResBij := by
  intro q i Y X f hY hX ⟨ζ⟩
  have : NeZero q := ⟨fun h0 => by
    subst h0
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
    have h := ζ.2.1
    simp only [Nat.cast_zero, isUnit_zero_iff] at h
    exact zero_ne_one h⟩
  have h1 := gen_bij (i := i) hT ζ
  have h2 := gen_bij (i := i) hT (ζ.map f.appTop.hom)
  have e : (Sec.res (F := tw q i) f) ∘ (fun k : ZMod q => k.val • twGen i ζ) =
      fun k : ZMod q => k.val • twGen i (ζ.map f.appTop.hom) := by
    funext k
    simp only [Function.comp]
    rw [res_nsmul', (hT q i).2.2.2.1]
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

end LateralTheory.E.ResBijPf
