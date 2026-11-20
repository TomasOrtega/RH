import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp R}

/- English proof (translation)
Rewrite using `[map_add, o.act.add, MonObj.comp_mul]`.
-/
private theorem act_add' (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) (a a' : 𝓞 D.F) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a + a')) =
      (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) * (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a')) := by
  rw [map_add, o.act.add, MonObj.comp_mul]

/- English proof (translation)
Rewrite using `[map_mul, o.act.mul, Category.assoc]`.
-/
private theorem act_mul' (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) (a a' : 𝓞 D.F) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (a * a')) =
      (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := by
  rw [map_mul, o.act.mul, Category.assoc]

/- English proof (translation)
Rewrite using `[map_one, o.act.one, Category.comp_id]`.
-/
private theorem act_one' (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O 1) = g := by
  rw [map_one, o.act.one, Category.comp_id]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `act_add' o g 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[Nat.cast_zero, pow_zero]`.

Conclude with `left_eq_mul.mp h`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ, act_add', ih, act_one', pow_succ]`.
-/
private theorem act_nat (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) (n : ℕ) :
    g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) = g ^ n := by
  induction n with
  | zero =>
    have h := act_add' o g 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, act_add', ih, act_one', pow_succ]

/- English proof (translation)
Establish `h1 : (1 : 𝓞 D.F) ∈ I ⊔ J` using `h ▸ Submodule.mem_top`. Take `⟨i, hi, j, hj, hij⟩` from `Submodule.mem_sup.mp h1`. Rewrite using `[← act_one' o g, ← hij, act_add', hI i hi, hJ j hj, _root_.mul_one]`.
-/
private theorem eq_one_of_killed (o : Obj b N s) {I J : Ideal (𝓞 D.F)} (h : I ⊔ J = ⊤) {T : Over S} {g : T ⟶ o.A}
    (hI : KilledBy o I g) (hJ : KilledBy o J g) : g = 1 := by
  have h1 : (1 : 𝓞 D.F) ∈ I ⊔ J := h ▸ Submodule.mem_top
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
  rw [← act_one' o g, ← hij, act_add', hI i hi, hJ j hj, _root_.mul_one]

/- English proof (translation)
Take `⟨hfin, -, hsurj⟩` from `GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA c hc`. Take `⟨t, ht⟩` from `ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.fst g.left (mulN A c).left)`. Establish `hsq : pullback.fst g.left (mulN A c).left ≫ g.left = pullback.snd g.left (mulN A c).left ≫ (mulN A c).left` using `pullback.condition`. Establish `hw : (t ≫ pullback.snd g.left (mulN A c).left) ≫ A.hom = x`. Establish `e1` using `Over.w (mulN A c)`.

Establish `e2` using `Over.w g`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc (pullback.snd _ _), ← hsq, Category.assoc]`. Use `_ = x := by rw [e2, ← Category.assoc, ht, Category.id_comp]; rfl`. Use `⟨Over.homMk (t ≫ pullback.snd g.left (mulN A c).left) hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Category.comp_id (Over.homMk _ hw), ← MonObj.comp_pow, ← GlobalTheory.MulFlatSurj.mulN_eq_pow]`. Use `ext1`. Simplify using `only [Over.comp_left, Over.homMk_left, Category.assoc]`. Rewrite using `[← hsq, ← Category.assoc, ht]`. Conclude with `Category.id_comp _`.
-/
private theorem exists_pow_eq (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {c : ℕ} (hc : 0 < c)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (g : Over.mk x ⟶ A) :
    ∃ v : Over.mk x ⟶ A, v ^ c = g := by
  obtain ⟨hfin, -, hsurj⟩ := GlobalTheory.KthRoot.finite_flat_surjective_mulN_any S A hA c hc
  obtain ⟨t, ht⟩ := ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_section (pullback.fst g.left (mulN A c).left)
  have hsq : pullback.fst g.left (mulN A c).left ≫ g.left = pullback.snd g.left (mulN A c).left ≫ (mulN A c).left :=
    pullback.condition
  have hw : (t ≫ pullback.snd g.left (mulN A c).left) ≫ A.hom = x := by
    have e1 := Over.w (mulN A c)
    have e2 := Over.w g
    calc (t ≫ pullback.snd g.left (mulN A c).left) ≫ A.hom
        = t ≫ pullback.snd g.left (mulN A c).left ≫ (mulN A c).left ≫ A.hom := by rw [e1, Category.assoc]
      _ = t ≫ pullback.fst g.left (mulN A c).left ≫ g.left ≫ A.hom := by
          rw [← Category.assoc (pullback.snd _ _), ← hsq, Category.assoc]
      _ = x := by rw [e2, ← Category.assoc, ht, Category.id_comp]; rfl
  refine ⟨Over.homMk (t ≫ pullback.snd g.left (mulN A c).left) hw, ?_⟩
  rw [← Category.comp_id (Over.homMk _ hw), ← MonObj.comp_pow, ← GlobalTheory.MulFlatSurj.mulN_eq_pow]
  ext1
  simp only [Over.comp_left, Over.homMk_left, Category.assoc]
  rw [← hsq, ← Category.assoc, ht]
  exact Category.id_comp _

end

/- English proof (translation)
Introduce `hsplit p _ D R _ b N r w 𝔞 ρ hcop he S s c o o' ψ hψ hker lv hlv`. Take `⟨e, he⟩` from `he`. Establish `hc : 0 < c` using `hψ.pos`. Take `⟨-, hmon, hcomm, -, -, ψ', hmon', h1, h2⟩` from `hψ`. Take `⟨hadd, hlin, hwsub, hgeom⟩` from `hlv`.

Establish `hcopρ : 𝔞 ^ ρ ⊔ w = ⊤`. Rewrite using `[sup_comm]`. Conclude with `Ideal.sup_pow_eq_top (by rw [sup_comm]; exact hcop)`. Establish `hle : uIdeal D r ^ (e * ρ) ≤ 𝔞 ^ ρ`. Rewrite using `[pow_mul]`.

Conclude with `Ideal.pow_right_mono he ρ`. Establish `hlvK : ∀ y, KilledBy o (𝔞 ^ ρ) (lv y)`. Introduce `y a ha`. Rewrite using `[← hlin]`. Conclude with `hwsub _ (Submodule.subset_span ⟨a, ha, y, rfl⟩)`.

Establish `hfix : ∀ {X : Over S} (oo : GlobalTheory.UPel.HT.Obj b N s) (g : X ⟶ oo.A) (β : 𝓞 D.F), β - 1 ∈ 𝔞 ^ ρ → KilledBy oo (𝔞 ^ ρ) g → g ≫ oo.act.act (algebraMap (𝓞 D.F) D.O β) = g`. Introduce `X oo g β hβ hg`. Establish `h3` using `act_add' oo g (β - 1) 1`. Rewrite `h3` using `[sub_add_cancel]`. Rewrite using `[h3, hg _ hβ, act_one', _root_.one_mul]`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y dsimp only`. Rewrite using `[hadd, MonObj.mul_comp]`. Introduce `c' x dsimp only`. Rewrite using `[hlin, Category.assoc, hcomm, Category.assoc]`.

Introduce `x hx dsimp only`. Rewrite using `[hwsub x hx, MonObj.one_comp]`. Introduce `kk _ _ xx`. Take `⟨hinj, hsurj⟩` from `hgeom kk xx`. Prove the components needed by the constructor for the conclusion.

Introduce `y hy`. Apply `hinj y` to reduce the goal to its premises. Establish `hI : KilledBy o (𝔞 ^ ρ) (toUnit (Over.mk xx) ≫ lv y)`. Introduce `a ha`. Rewrite using `[Category.assoc, hlvK y a ha, MonObj.comp_one]`.

Establish `hJ : KilledBy o w (toUnit (Over.mk xx) ≫ lv y)`. Use `hker _ _ ⟨?_, e * ρ, fun a ha => hI a (hle ha)⟩` and prove the remaining obligations. Rewrite using `[Category.assoc]`. Conclude with `hy`. Conclude with `eq_one_of_killed o hcopρ hI hJ`.

Introduce `g' hg'`. Take `⟨u0, hu0⟩` from `exists_pow_eq o'.A o'.ab hc xx g'`. Establish `hpre : (u0 ≫ ψ') ≫ ψ = g'`. Rewrite using `[Category.assoc, h2, MonObj.comp_pow, Category.comp_id, hu0]`. Establish `hkill : ∀ {X : Over S} (z : X ⟶ o.A), z ≫ ψ = 1 → z ^ c = 1`.

Introduce `X z hz`. Rewrite using `[← Category.comp_id z, ← MonObj.comp_pow, ← h1, ← Category.assoc, hz, MonObj.one_comp]`. Establish `hc0 : ((c : ℕ) : 𝓞 D.F) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Take `⟨m, α, hα1, hαm⟩` from `hsplit (𝓞 D.F) (uIdeal D r) (c : 𝓞 D.F) hc0 (e * ρ)`. Establish `h1top : (1 : 𝓞 D.F) ∈ 𝔞 ^ ρ ⊔ w` using `hcopρ ▸ Submodule.mem_top`.

Take `⟨v, hv, u, hu, hvu⟩` from `Submodule.mem_sup.mp h1top`. Use `set h0 := u0 ≫ ψ' with hh0`. Establish `hA : ∀ a ∈ 𝔞 ^ ρ, (h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ ψ = 1`. Introduce `a ha`. Rewrite using `[Category.assoc, hcomm, ← Category.assoc, hpre]`.

Conclude with `hg' a ha`. Establish `hB : ∀ a ∈ 𝔞 ^ ρ, KilledBy o w ((h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O α))`. Introduce `a ha`. Use `hker _ _ ⟨?_, m, ?_⟩` and prove the remaining obligations. Use `haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O α)`.

Rewrite using `[Category.assoc, hcomm, ← Category.assoc, hA a ha, MonObj.one_comp]`. Introduce `bb hbb`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp (hαm bb hbb)`. Rewrite using `[← act_mul', ← act_mul']`. Establish `hre : bb * α * a = t * ((c : 𝓞 D.F) * a)` using `by linear_combination (-a) * ht`.

Rewrite using `[hre, act_mul', act_mul', act_nat, hkill _ (hA a ha)]`. Use `haveI := o.act.hom (algebraMap (𝓞 D.F) D.O t)`. Conclude with `MonObj.one_comp _`. Establish `hK : KilledBy o (𝔞 ^ ρ) ((h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O α)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O u))`. Introduce `a ha`.

Rewrite using `[← act_mul', ← act_mul', show a * u * α = u * (α * a) by ring, act_mul', act_mul']`. Conclude with `hB a ha u hu`. Take `⟨y, hy⟩` from `hsurj _ hK`. Use `⟨y, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← Category.assoc, hy, Category.assoc, hcomm, ← Category.assoc, Category.assoc h0, hcomm, ← Category.assoc, hpre]`. Establish `hα' : α - 1 ∈ 𝔞 ^ ρ` using `hle hα1`. Establish `hu' : u - 1 ∈ 𝔞 ^ ρ`. Establish `: u - 1 = -v` using `by linear_combination hvu`. Rewrite using `[this]`.

Conclude with `(𝔞 ^ ρ).neg_mem hv`. Rewrite using `[hfix o' g' α hα' hg', hfix o' g' u hu' hg']`.
-/
theorem levPush_of : IdealSplit → LevPush := by
  intro hsplit p _ D R _ b N r w 𝔞 ρ hcop he S s c o o' ψ hψ hker lv hlv
  obtain ⟨e, he⟩ := he
  have hc : 0 < c := hψ.pos
  obtain ⟨-, hmon, hcomm, -, -, ψ', hmon', h1, h2⟩ := hψ
  obtain ⟨hadd, hlin, hwsub, hgeom⟩ := hlv
  have hcopρ : 𝔞 ^ ρ ⊔ w = ⊤ := by
    rw [sup_comm]
    exact Ideal.sup_pow_eq_top (by rw [sup_comm]; exact hcop)
  have hle : uIdeal D r ^ (e * ρ) ≤ 𝔞 ^ ρ := by
    rw [pow_mul]
    exact Ideal.pow_right_mono he ρ
  have hlvK : ∀ y, KilledBy o (𝔞 ^ ρ) (lv y) := by
    intro y a ha
    rw [← hlin]
    exact hwsub _ (Submodule.subset_span ⟨a, ha, y, rfl⟩)
  have hfix : ∀ {X : Over S} (oo : GlobalTheory.UPel.HT.Obj b N s) (g : X ⟶ oo.A) (β : 𝓞 D.F), β - 1 ∈ 𝔞 ^ ρ →
      KilledBy oo (𝔞 ^ ρ) g → g ≫ oo.act.act (algebraMap (𝓞 D.F) D.O β) = g := by
    intro X oo g β hβ hg
    have h3 := act_add' oo g (β - 1) 1
    rw [sub_add_cancel] at h3
    rw [h3, hg _ hβ, act_one', _root_.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [hadd, MonObj.mul_comp]
  · intro c' x
    dsimp only
    rw [hlin, Category.assoc, hcomm, Category.assoc]
  · intro x hx
    dsimp only
    rw [hwsub x hx, MonObj.one_comp]
  · intro kk _ _ xx
    obtain ⟨hinj, hsurj⟩ := hgeom kk xx
    constructor
    · intro y hy
      apply hinj y
      have hI : KilledBy o (𝔞 ^ ρ) (toUnit (Over.mk xx) ≫ lv y) := by
        intro a ha
        rw [Category.assoc, hlvK y a ha, MonObj.comp_one]
      have hJ : KilledBy o w (toUnit (Over.mk xx) ≫ lv y) := by
        refine hker _ _ ⟨?_, e * ρ, fun a ha => hI a (hle ha)⟩
        rw [Category.assoc]
        exact hy
      exact eq_one_of_killed o hcopρ hI hJ
    · intro g' hg'
      obtain ⟨u0, hu0⟩ := exists_pow_eq o'.A o'.ab hc xx g'
      have hpre : (u0 ≫ ψ') ≫ ψ = g' := by
        rw [Category.assoc, h2, MonObj.comp_pow, Category.comp_id, hu0]
      have hkill : ∀ {X : Over S} (z : X ⟶ o.A), z ≫ ψ = 1 → z ^ c = 1 := by
        intro X z hz
        rw [← Category.comp_id z, ← MonObj.comp_pow, ← h1, ← Category.assoc, hz, MonObj.one_comp]
      have hc0 : ((c : ℕ) : 𝓞 D.F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      obtain ⟨m, α, hα1, hαm⟩ := hsplit (𝓞 D.F) (uIdeal D r) (c : 𝓞 D.F) hc0 (e * ρ)
      have h1top : (1 : 𝓞 D.F) ∈ 𝔞 ^ ρ ⊔ w := hcopρ ▸ Submodule.mem_top
      obtain ⟨v, hv, u, hu, hvu⟩ := Submodule.mem_sup.mp h1top
      set h0 := u0 ≫ ψ' with hh0
      have hA : ∀ a ∈ 𝔞 ^ ρ, (h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ ψ = 1 := by
        intro a ha
        rw [Category.assoc, hcomm, ← Category.assoc, hpre]
        exact hg' a ha
      have hB : ∀ a ∈ 𝔞 ^ ρ, KilledBy o w ((h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫
          o.act.act (algebraMap (𝓞 D.F) D.O α)) := by
        intro a ha
        refine hker _ _ ⟨?_, m, ?_⟩
        · haveI := o'.act.hom (algebraMap (𝓞 D.F) D.O α)
          rw [Category.assoc, hcomm, ← Category.assoc, hA a ha, MonObj.one_comp]
        · intro bb hbb
          obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hαm bb hbb)
          rw [← act_mul', ← act_mul']
          have hre : bb * α * a = t * ((c : 𝓞 D.F) * a) := by linear_combination (-a) * ht
          rw [hre, act_mul', act_mul', act_nat, hkill _ (hA a ha)]
          haveI := o.act.hom (algebraMap (𝓞 D.F) D.O t)
          exact MonObj.one_comp _
      have hK : KilledBy o (𝔞 ^ ρ) ((h0 ≫ o.act.act (algebraMap (𝓞 D.F) D.O α)) ≫
          o.act.act (algebraMap (𝓞 D.F) D.O u)) := by
        intro a ha
        rw [← act_mul', ← act_mul', show a * u * α = u * (α * a) by ring, act_mul', act_mul']
        exact hB a ha u hu
      obtain ⟨y, hy⟩ := hsurj _ hK
      refine ⟨y, ?_⟩
      dsimp only
      rw [← Category.assoc, hy, Category.assoc, hcomm, ← Category.assoc, Category.assoc h0, hcomm,
        ← Category.assoc, hpre]
      have hα' : α - 1 ∈ 𝔞 ^ ρ := hle hα1
      have hu' : u - 1 ∈ 𝔞 ^ ρ := by
        have : u - 1 = -v := by linear_combination hvu
        rw [this]
        exact (𝔞 ^ ρ).neg_mem hv
      rw [hfix o' g' α hα' hg', hfix o' g' u hu' hg']

end UpperTheory.Gal.crystallineComparison.Mod
