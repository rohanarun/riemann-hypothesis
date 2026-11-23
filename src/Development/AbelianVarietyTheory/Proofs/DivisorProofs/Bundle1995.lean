module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulShortNonneg
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IndexRangeMatrix
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1716
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0396
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1944
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardExtendOfLocallyTrivialNormalCodimTwo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtendClass

open GlobalTheory.GlueLineBundle TopologicalSpace

variable {X : Scheme.{0}}

theorem gm_eq_map {Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (hy : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm f y U a = Units.map (f.stalkMap y).hom.toMonoidHom (gm (𝟙 X) (f y) U a) := by
  apply Units.ext
  rw [gm_val f y U hy, Units.coe_map, gm_val (𝟙 X) (f y) U hy]
  show _ = (f.stalkMap y).hom ((X.presheaf.germ U (f y) hy).hom a.val)
  rw [Scheme.Hom.germ_stalkMap_apply]

theorem map_stalk_inj {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (y : Y) :
    Function.Injective (Units.map (j.stalkMap y).hom.toMonoidHom) :=
  Units.map_injective (f := (j.stalkMap y).hom.toMonoidHom)
    (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv.injective

theorem exists_res_eq {U V : X.Opens} (h : V ≤ U) (hb : Function.Bijective (resG X h)) (u : Γ(X, V)ˣ) :
    ∃ a : Γ(X, U)ˣ, res h a = u := by
  obtain ⟨a, ha⟩ := hb.2 u.val
  obtain ⟨b, hb'⟩ := hb.2 u.inv
  have e1 : a * b = 1 := hb.1 (by rw [map_mul, map_one, ha, hb']; exact u.val_inv)
  exact ⟨⟨a, b, e1, (mul_comm _ _).trans e1⟩, Units.ext ha⟩

theorem eq_of_gm_ι (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ w : W.toScheme, W.ι w ∈ V → gm W.ι w V a = gm W.ι w V b) : a = b := by
  have e : res (inf_le_left : V ⊓ W ≤ V) a = res inf_le_left b := by
    apply unit_ext_imm
    intro x hx
    have hxW : x ∈ W := hx.2
    have hxV : x ∈ V := hx.1
    have hx' : W.ι ⟨x, hxW⟩ ∈ V ⊓ W := hx
    refine ⟨_, W.ι, inferInstance, ⟨x, hxW⟩, rfl, ?_⟩
    exact (gm_res W.ι _ inf_le_left hx' a).trans ((h _ hxV).trans (gm_res W.ι _ inf_le_left hx' b).symm)
  exact Units.ext ((hW V).1 (congrArg Units.val e))

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem exists_sigma (W : X.Opens) {M : LB W.toScheme} (N : X.Opens)
    (t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)))) (ht : t.IsGen) :
    ∃ σ : ∀ k, Γ(W.toScheme, W.ι ⁻¹ᵁ N ⊓ M.U k)ˣ, ∀ (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N → z ∈ M.U k →
      z ∈ M.U k' → gm (𝟙 _) z _ (σ k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ k') := by
  revert t
  set ι₁ := X.homOfLE (inf_le_right : N ⊓ W ≤ W) with hι₁
  intro t ht
  have pre : ∀ z : W.toScheme, W.ι z ∈ N → ∃ a : (N ⊓ W : X.Opens).toScheme, ι₁ a = z := fun z hz =>
    ⟨⟨z.1, hz, z.2⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  have hle : ∀ k, W.ι ⁻¹ᵁ N ⊓ M.U k ≤ ι₁ ''ᵁ (M.pull ι₁).U (fun _ => k) := fun k z hz => by
    obtain ⟨a, rfl⟩ := pre z hz.1
    exact ι₁.apply_mem_image_iff.2 (mem_pull.2 hz.2)
  refine ⟨fun k => res (hle k) (imU ι₁ _ (t.s fun _ => k)), fun z k k' hz hk hk' => ?_⟩
  obtain ⟨a, rfl⟩ := pre z hz
  have ev : ∀ k, ι₁ a ∈ M.U k → gm ι₁ a (W.ι ⁻¹ᵁ N ⊓ M.U k) (res (hle k) (imU ι₁ _ (t.s fun _ => k))) =
      gm (𝟙 _) a _ (t.s fun _ => k) := fun k hk => by
    have hm : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
    rw [gm_res ι₁ a (hle k) hm]
    have := gm_imU ι₁ (𝟙 _) a ((M.pull ι₁).U fun _ => k) (mem_pull.2 hk) (t.s fun _ => k)
    rwa [Category.id_comp] at this
  have eg : gm ι₁ a (M.U k ⊓ M.U k') (M.g k k') = gm (𝟙 _) a _ ((M.pull ι₁).g (fun _ => k) (fun _ => k')) := by
    have := gm_pull_g M ι₁ (𝟙 _) a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')
    rw [Category.id_comp] at this
    exact this.symm
  have m1 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k := ⟨hz, hk⟩
  have m2 : ι₁ a ∈ M.U k ⊓ M.U k' := ⟨hk, hk'⟩
  have m3 : ι₁ a ∈ W.ι ⁻¹ᵁ N ⊓ M.U k' := ⟨hz, hk'⟩
  apply map_stalk_inj ι₁ a
  beta_reduce
  rw [map_mul, ← gm_eq_map ι₁ a _ m1, ← gm_eq_map ι₁ a _ m2, ← gm_eq_map ι₁ a _ m3,
    ev k hk, ev k' hk', eg]
  exact (isGen_iff_germ t).1 ht a (fun _ => k) (fun _ => k') (mem_pull.2 hk) (mem_pull.2 hk')

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace
variable {X : Scheme.{0}}

theorem mul_ringHom_units_ratio {G : Type} [CommGroup G] (g a b : G) : g * a * (g * b)⁻¹ = a * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (W : X.Opens) {M : LB W.toScheme} (hM : M.IsLB) {I : Type} (N : I → X.Opens)
    (σ : ∀ x k, Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ M.U k)ˣ)
    (hσ : ∀ x (z : W.toScheme) (k k' : M.ι), W.ι z ∈ N x → z ∈ M.U k → z ∈ M.U k' →
      gm (𝟙 _) z _ (σ x k) = gm (𝟙 _) z (M.U k ⊓ M.U k') (M.g k k') * gm (𝟙 _) z _ (σ x k')) (x y : I) :
    ∃ r : Γ(W.toScheme, W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y)ˣ, ∀ (z : W.toScheme) (k : M.ι), W.ι z ∈ N x → W.ι z ∈ N y →
      z ∈ M.U k → gm (𝟙 _) z _ r = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := by
  let O : M.ι → W.toScheme.Opens := fun k => W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y ⊓ M.U k
  have l0 : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ W.ι ⁻¹ᵁ N y := fun k => inf_le_left
  have lx : ∀ k, O k ≤ W.ι ⁻¹ᵁ N x ⊓ M.U k := fun k z hz => ⟨hz.1.1, hz.2⟩
  have ly : ∀ k, O k ≤ W.ι ⁻¹ᵁ N y ⊓ M.U k := fun k z hz => ⟨hz.1.2, hz.2⟩
  have ev : ∀ k (z : W.toScheme) (hz : z ∈ O k),
      gm (𝟙 _) z (O k) (res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹) =
        gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ := fun k z hz => by
    rw [map_mul, map_inv, gm_res _ z (ly k) hz, gm_res _ z (lx k) hz]
  obtain ⟨r, hr⟩ := glue_unit _ O l0 (fun z hz => by
      obtain ⟨k, hk⟩ := exists_chart hM z
      exact Opens.mem_iSup.2 ⟨k, show z ∈ O k from ⟨hz, hk⟩⟩) (fun k => res (ly k) (σ y k) * (res (lx k) (σ x k))⁻¹)
    (fun k k' z hz => by
      have h1 : z ∈ O k := hz.1
      have h2 : z ∈ O k' := hz.2
      have hx : W.ι z ∈ N x := h1.1.1
      have hy : W.ι z ∈ N y := h1.1.2
      have hk : z ∈ M.U k := h1.2
      have hk' : z ∈ M.U k' := h2.2
      rw [ev k z h1, ev k' z h2, hσ x z k k' hx hk hk', hσ y z k k' hy hk hk', mul_ringHom_units_ratio])
  refine ⟨r, fun z k hx hy hk => ?_⟩
  have hz : z ∈ O k := ⟨⟨hx, hy⟩, hk⟩
  rw [← gm_res _ z (l0 k) hz, hr k, ev k z hz]

theorem exists_ext (W : X.Opens) (hW : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)))
    (P Q : X.Opens) (r : Γ(W.toScheme, W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q)ˣ) :
    ∃ g : Γ(X, P ⊓ Q)ˣ, ∀ z : W.toScheme, W.ι z ∈ P → W.ι z ∈ Q → gm W.ι z (P ⊓ Q) g = gm (𝟙 _) z _ r := by
  have hle : P ⊓ Q ⊓ W ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q) := fun p hp => by
    have hpW : p ∈ W := hp.2
    have hpP : p ∈ P := hp.1.1
    have hpQ : p ∈ Q := hp.1.2
    have hm : (⟨p, hpW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q := ⟨hpP, hpQ⟩
    exact W.ι.apply_mem_image_iff.2 hm
  obtain ⟨g, hg⟩ := exists_res_eq (inf_le_left : P ⊓ Q ⊓ W ≤ P ⊓ Q) (hW _) (res hle (imU W.ι _ r))
  refine ⟨g, fun z hP hQ => ?_⟩
  have hz : W.ι z ∈ P ⊓ Q ⊓ W := ⟨⟨hP, hQ⟩, z.2⟩
  rw [← gm_res W.ι z inf_le_left hz, hg, gm_res W.ι z hle hz]
  have := gm_imU W.ι (𝟙 _) z _ (show z ∈ W.ι ⁻¹ᵁ P ⊓ W.ι ⁻¹ᵁ Q from ⟨hP, hQ⟩) r
  rwa [Category.id_comp] at this

end GlobalTheory.ExtendClass

namespace GlobalTheory.ExtendClass
open GlobalTheory.GlueLineBundle TopologicalSpace

theorem commGroup_cocycle_mul_inv_mul_mul_inv {G : Type} [CommGroup G] (a b c : G) : b * a⁻¹ * (c * b⁻¹) = c * a⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commGroup_inv_eq_conj_twist_identity {G : Type} [CommGroup G] (a b g : G) : a⁻¹ = g * b * a⁻¹ * g⁻¹ * b⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.ExtendClass


open GlobalTheory.GlueLineBundle TopologicalSpace GlobalTheory.ExtendClass in
theorem GlobalTheory.extend_class_of_locally_trivial : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ W : X.Opens, (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic W.toScheme, (∀ x : X, ∃ N : X.Opens, x ∈ N ∧ GlobalTheory.CechPic.pull (X.homOfLE (inf_le_right : N ⊓ W ≤ W)) c = 0) → ∃ c' : Pic X, GlobalTheory.CechPic.pull W.ι c' = c := by
  intro X _ hX W hW c hc
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have hbij : ∀ V : X.Opens, Function.Bijective (resG X (inf_le_left : V ⊓ W ≤ V)) :=
    ((extension_over_codim_two X hX).1 W hW).1
  choose N hN ht using hc
  have ht' : ∀ x, ∃ t : LB.Gen (M.pull (X.homOfLE (inf_le_right : N x ⊓ W ≤ W))), t.IsGen := fun x =>
    (cls_eq_zero_iff (pull_isLB hM _)).1 (ht x)
  choose t htg using ht'
  choose σ hσ using fun x => exists_sigma W (N x) (t x) (htg x)
  choose r hr using exists_ratio W hM N σ hσ
  choose g hg using fun x y => exists_ext W hbij (N x) (N y) (r x y)
  let L : LB X := ⟨↥X, N, g⟩
  have hgr : ∀ x y (z : W.toScheme) k, W.ι z ∈ N x → W.ι z ∈ N y → z ∈ M.U k →
      gm W.ι z (N x ⊓ N y) (g x y) = gm (𝟙 _) z _ (σ y k) * (gm (𝟙 _) z _ (σ x k))⁻¹ :=
    fun x y z k hx hy hk => (hg x y z hx hy).trans (hr x y z k hx hy hk)
  have hL : L.IsLB :=
    { cover := top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hN x⟩
      g_self := fun x => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        dsimp only [L]
        rw [gm_res W.ι z _ hz, map_one]
        exact (hgr x x z k hz hz hk).trans (mul_inv_cancel _)
      cocycle := fun x y w => eq_of_gm_ι W hbij fun z hz => by
        obtain ⟨k, hk⟩ := exists_chart hM z
        have hx : W.ι z ∈ N x := hz.1.1
        have hy : W.ι z ∈ N y := hz.1.2
        have hw : W.ι z ∈ N w := hz.2
        have h1 : W.ι z ∈ N x ⊓ N y := ⟨hx, hy⟩
        have h2 : W.ι z ∈ N y ⊓ N w := ⟨hy, hw⟩
        have h3 : W.ι z ∈ N x ⊓ N w := ⟨hx, hw⟩
        dsimp only [L] at hz ⊢
        rw [map_mul, gm_res W.ι z _ hz, gm_res W.ι z _ hz, gm_res W.ι z _ hz]
        rw [hgr x y z k hx hy hk, hgr y w z k hy hw hk, hgr x w z k hx hw hk, commGroup_cocycle_mul_inv_mul_mul_inv] }
  have hle : ∀ p : (PUnit → L.ι) × M.ι, (L.pull W.ι).U p.1 ⊓ M.U p.2 ≤ W.ι ⁻¹ᵁ N (p.1 PUnit.unit) ⊓ M.U p.2 :=
    fun p z hz => ⟨mem_pull.1 hz.1, hz.2⟩
  let w : LB.Iso M (L.pull W.ι) := ⟨fun p => res (hle p) (σ (p.1 PUnit.unit) p.2)⁻¹⟩
  have ew : ∀ (p : (PUnit → L.ι) × M.ι) (z : W.toScheme) (hz : z ∈ (L.pull W.ι).U p.1 ⊓ M.U p.2),
      gm (𝟙 _) z _ (w.s p) = (gm (𝟙 _) z _ (σ (p.1 PUnit.unit) p.2))⁻¹ := fun p z hz =>
    (gm_res _ z (hle p) hz _).trans (map_inv _ _)
  have hw : w.IsGen := by
    rintro ⟨J, k⟩ ⟨J', k'⟩
    apply unit_ext
    intro z hz
    have hj : W.ι z ∈ L.U (J PUnit.unit) := mem_pull.1 hz.1.1
    have hj' : W.ι z ∈ L.U (J' PUnit.unit) := mem_pull.1 hz.2.1
    have hk : z ∈ M.U k := hz.1.2
    have hk' : z ∈ M.U k' := hz.2.2
    have e := gm_div_g (L := L) (L' := M) (F := W.ι) (𝟙 _) z (J PUnit.unit) (J' PUnit.unit) k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    have e' : gm (𝟙 _) z _ ((LB.div (L.pull W.ι) M).g (J, k) (J', k')) = _ := e
    refine (gm_res _ z inf_le_left hz _).trans ?_
    rw [map_mul, gm_res _ z inf_le_right hz, e', ew _ z hz.1, ew _ z hz.2]
    show _ = gm W.ι z (N (J PUnit.unit) ⊓ N (J' PUnit.unit)) (g (J PUnit.unit) (J' PUnit.unit)) * _ * _
    rw [hgr _ _ z k hj hj' hk, hσ (J' PUnit.unit) z k k' hj' hk hk']
    exact commGroup_inv_eq_conj_twist_identity _ _ _
  refine ⟨cls L hL, ?_⟩
  rw [← cls_pull hL W.ι (pull_isLB hL _)]
  exact (cls_eq_iff _ _).2 (LBIso.symm ⟨w, hw⟩)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClearingIntegerShortSeriesIntegralCoprimeLevelStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open GlobalTheory.CovInt IsDedekindDomain
open MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv GlobalTheory.IntCuspLat GlobalTheory.ShortBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.clearingInteger_shortSeries_integral_coprimeLevel : ∀ (D : D7) (H : Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)], d.IsLev → IsNab d.Xo₂ d.c₂ d.nab₂ → (∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ = 1) → (∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) → d.l₂.M ≠ 0 → ∀ (Λ : GenLat D.host.E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ w → ∀ (x0 : Fin n → Dw.La) (g : Rul Xo c), g ∈ sec Xo c w n → IsShortRule Xo c d Λ N x0 P g → ∀ la : HeightOneSpectrum (𝓞 c.F), (∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → ¬ ℓ ∣ d.l₂.M) → ∀ s : c.F, Submodule.span (𝓞 c.F) {s} * ∏ τ : D.host.E →+* ℂ, idealAt c Λ.Ln τ ^ Dw.mult τ ≤ ∏ τ : D.host.E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ → ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v ((s * betaH (Dw := Dw) c Λ * (intZ D Dw d.l₂ n w : c.F)) • g) := by
  first | exact @GlobalTheory.CovInt.smul_intZ_nonneg_coprime | exact GlobalTheory.CovInt.smul_intZ_nonneg_coprime | (intros; apply GlobalTheory.CovInt.smul_intZ_nonneg_coprime <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointEigenbasisChangeDetIntegralAlmostAllPrime
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM fullB tv)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
open MonObj

theorem GlobalTheory.DetInt.det_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La →
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 z.K)), ∀ p ∉ S, ∀ (T : CDVR) (iK : z.K →+* T.Fr), T.FinRes →
      (∀ y : z.K, iK y ∈ Set.range (algebraMap T.V T.Fr) ↔ p.valuation z.K y ≤ 1) → ∀ (M : GlobalTheory.LamT.LocMod z T iK),
      letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
      ∀ (φ : z.K →ₐ[c.F] T.Fr) (yT y' : FrPt Xo c T.Fr)
        (g : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T.Fr) (a : T.Fr),
        φ.toRingHom = iK → FrMap φ z.y yT → GlobalTheory.Frames.FrChg g a yT y' → (∀ b, IsUnit (g b).det) →
        GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F z.K)) M.m1 M.m2 y'.u →
        (∏ b, (g b).det) ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.LocGenVal.valuation_div_le_one_cofinite z.K z.LamL.I z.U.det
  refine ⟨S, fun p hp T iK _hfin hval M => ?_⟩
  letI := (iK.comp (algebraMap c.F z.K)).toAlgebra
  intro φ yT y' g a hφ hmap hchg hg hint
  obtain ⟨A, hA, hloc⟩ := hz.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 p
  obtain ⟨nu, mu, C, hCint, hU, hAmu, hC⟩ :=
    GlobalTheory.T.tangent_letters_integralLieBasis_eigenframe_relation E H Dw l Xo c z f La hz p T iK M hval A hA φ yT y' g a hφ hmap hchg hg hint
  let Cv : Matrix (Fin z.Φ.T.g) (Fin z.Φ.T.g) T.V := Matrix.of fun i k => (hCint (z.e.symm i) k).choose
  have hCv : Cv.map (algebraMap T.V T.Fr) = Matrix.of fun i k => C (z.e.symm i) k := by
    ext i k; exact (hCint (z.e.symm i) k).choose_spec
  obtain ⟨hUdet, hdet⟩ := GlobalTheory.T.det_block_change_of_basis_via_two_families_implicit Dw.mult z.e (fullB yT) (ReciprocityTheory.ChartRestriction.G.PullbackSections.fullB_basis yT) nu mu
    (z.U.map iK) (A.map iK) C g (by simpa using hU) (by simpa using hAmu) hC
  have e1 : (z.U.map iK).det = iK z.U.det := (RingHom.map_det iK z.U).symm
  have e2 : (A.map iK).det = iK A.det := (RingHom.map_det iK A).symm
  have e3 : (Cv.map (algebraMap T.V T.Fr)).det = algebraMap T.V T.Fr Cv.det := (RingHom.map_det _ Cv).symm
  rw [e1] at hUdet hdet
  rw [e2] at hdet
  have hU0 : z.U.det ≠ 0 := fun h => hUdet (by rw [h, map_zero])
  obtain ⟨r, hr⟩ := (hval _).2 (hS p hp A.det hloc hU0)
  refine ⟨Cv.det * r, ?_⟩
  rw [map_mul, ← e3, hCv, hr, map_div₀, ← mul_div_assoc, div_eq_iff hUdet, hdet]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnPolynomialLocalDepthEqPlaceDepthStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnPolynomial_localDepth_eq_placeDepth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  first | exact @GlobalTheory.ColDepth.nuLocOf_eq_nuP | exact GlobalTheory.ColDepth.nuLocOf_eq_nuP | (intros; apply GlobalTheory.ColDepth.nuLocOf_eq_nuP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilGeneric

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_of_generic : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  intro O _ _ A _ _ hA P hP h₁ h₂ hamp N hN _ u v hu hv c k₀ _ j hj H k _ ρ
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  let pc {T : Over (Sp O)} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)
  have hB : ∀ (T : Over (Sp O)) (x x' y : T ⟶ A), pc (x * x') y = pc x y + pc x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over (Sp O)) (x y y' : T ⟶ A), pc x (y * y') = pc x y + pc x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have pc_pow_left : ∀ {T : Over (Sp O)} (x y : T ⟶ A) (k : ℕ), pc (x ^ k) y = k • pc x y := by
    intro T x y k
    have one : pc (1 : T ⟶ A) y = 0 := by
      have e := hB T 1 1 y
      rwa [_root_.mul_one, left_eq_add] at e
    induction k with
    | zero => rw [pow_zero, one, zero_smul]
    | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]
  have pc_pow_right : ∀ {T : Over (Sp O)} (x y : T ⟶ A) (k : ℕ), pc x (y ^ k) = k • pc x y := by
    intro T x y k
    have one : pc x (1 : T ⟶ A) = 0 := by
      have e := hB' T x 1 1
      rwa [_root_.mul_one, left_eq_add] at e
    induction k with
    | zero => rw [pow_zero, one, zero_smul]
    | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]
  have exists_theta_diag : ∀ {k : ℕ} {T : Over (Sp O)} (x : T ⟶ A), x ^ k = 1 →
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
    intro k T x hx
    have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc g g := fun g => by
      rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have h1 : k • pc (fst T A ≫ x) (fst T A ≫ x) = 0 := by
      rw [← pc_pow_left, ha]
      have e := hB (T ⊗ A) 1 1 (fst T A ≫ x)
      rwa [_root_.mul_one, left_eq_add] at e
    have h2 : k • pc (fst T A ≫ x) (snd T A) = 0 := by
      rw [← pc_pow_left, ha]
      have e := hB (T ⊗ A) 1 1 (snd T A)
      rwa [_root_.mul_one, left_eq_add] at e
    have h3 : k • pc (snd T A) (fst T A ≫ x) = 0 := by
      rw [← pc_pow_right, ha]
      have e := hB' (T ⊗ A) (snd T A) 1 1
      rwa [_root_.mul_one, left_eq_add] at e
    obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
      refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
      rw [cls_linComb hD, Fin.sum_univ_two]
      show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
      rw [e, e, hB, hB', hB']
      simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
      abel
    exact ⟨⟨x, t, ht⟩, rfl⟩
  have lifts : ∀ z : 𝟙_ (Over (Sp O)) ⟶ A, z ^ N = 1 → ∀ p : (𝟙_ (Over (Sp O))).left, ∃ V : (𝟙_ (Over (Sp O))).left.Opens,
      p ∈ V ∧ ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts u hu) (lifts v hv)
  obtain ⟨w, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 c₀
  have spec : ∀ (F : Type) [Field F] (σ : O →+* F), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N
      (toUnit (Over.mk (spMap σ)) ≫ u) (toUnit (Over.mk (spMap σ)) ≫ v) (unitOn (Units.map σ.toMonoidHom w)) := by
    intro F _ σ
    have hN' := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap σ))) hc₀
    have hl : (toUnit (Over.mk (spMap σ))).left = spMap σ := rfl
    rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN'
    exact hN'
  have e := GlobalTheory.Ex.Specialise.unitOn_bijective.1 (CommutatorPairing.weilIs_unique hG hA hD (spec k₀ j) H)
  have e' : w = c := Units.map_injective hj e
  rw [← e']
  exact spec k ρ

end GlobalTheory.WeilGeneric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueTimesThetaFramesChartGaugeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValueTimesThetaFrames_chartGauge : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g) (geo : Geo ν d) (x y z : Fin g → ℂ) (j : thK → D.P.L.ι), ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j → cubF d x y z * ∏ I : thK, geo.frG (j I) (wI x y z I) ^ thε I = valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val := by
  first | exact @GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | exact GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG | (intros; apply GlobalTheory.MBLow.Cl.CubHol.cubF_mul_prod_frG <;> assumption)
end

