module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormPullEqOfLbIsoPow
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormalFormArcDatumFramedPointRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
section
noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

def ArcZero (X : FlagCover Y) (Z : Comp Xo c) (la : AllWt.Weight Dw) (σ : c.F →+* ℂ)
    (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)) : Prop :=
  ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι), W ≤ (L₀ X Z la).U i →
    ∀ (ψ : ℂ → (Γ(Y₀ X Z, W) →+* ℂ)) (r : ℝ), IsHolPts ψ r →
      (∀ u ∈ Metric.ball (0 : ℂ) r, spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z =
        spMap σ) →
      (∀ s, (spMap (ψ 0) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) s ∈ bd₀ X Z) →
      (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 →
        ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ u in 𝓝[≠] (0 : ℂ),
        ∀ (hO : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ U₀ X Z)
          (hi : ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) ⁻¹ᵁ (L₀ X Z la).U i),
          ‖H0.val (spMap (ψ u) ≫ (show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec)) i hO hi m‖ < ε

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutationAtSmallPlace
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCommFrame


open Classical in
theorem exists_equiv_of_fibre_card {G : Type} [Group G] (K : Subgroup G) (A B : Finset G) (Tr : G → Prop)
    (hcount : ∀ c : G ⧸ K, ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card =
      ((B ×ˢ A).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card)
    (htr : ∀ s ∈ A, ∀ t ∈ B, ∀ t' ∈ B, ∀ s' ∈ A, (t' * s')⁻¹ * (s * t) ∈ K → Tr ((t' * s')⁻¹ * (s * t))) :
    ∃ σ : A × B ≃ B × A, ∀ x, Tr ((((σ x).1 : G) * (σ x).2)⁻¹ * ((x.1 : G) * x.2)) := by
  classical
  have fib : ∀ (A B : Finset G) (c : G ⧸ K),
      Fintype.card {x : A × B // (((x.1 : G) * x.2 : G) : G ⧸ K) = c} =
        ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : G) : G ⧸ K) = c)).card := by
    intro A B c
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun x => ⟨((x.1.1 : G), (x.1.2 : G)), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨x.1.1.2, x.1.2.2⟩, x.2⟩⟩
        invFun := fun y => ⟨(⟨y.1.1, (Finset.mem_product.1 (Finset.mem_filter.1 y.2).1).1⟩,
          ⟨y.1.2, (Finset.mem_product.1 (Finset.mem_filter.1 y.2).1).2⟩), (Finset.mem_filter.1 y.2).2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  let f : A × B → G ⧸ K := fun x => (((x.1 : G) * x.2 : G) : G ⧸ K)
  let g : B × A → G ⧸ K := fun x => (((x.1 : G) * x.2 : G) : G ⧸ K)
  have e : ∀ c, {x // f x = c} ≃ {y // g y = c} := fun c =>
    Fintype.equivOfCardEq (by rw [fib A B c, fib B A c]; convert hcount c)
  refine ⟨Equiv.ofFiberEquiv e, fun x => ?_⟩
  have h := Equiv.ofFiberEquiv_map e x
  have hK : (((Equiv.ofFiberEquiv e x).1 : G) * (Equiv.ofFiberEquiv e x).2)⁻¹ * ((x.1 : G) * x.2) ∈ K :=
    QuotientGroup.eq.1 h
  exact htr _ x.1.2 _ x.2.2 _ (Equiv.ofFiberEquiv e x).1.2 _ (Equiv.ofFiberEquiv e x).2.2 hK

theorem commAt_of {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : CommAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hc F i i'
  have hN : P.Nr = (Vc D j).rank := by simpa using Fintype.card_congr rk.toEquiv
  have hi1 : 1 ≤ i.1.2 := i.2.1
  have hi2 : i.1.2 ≤ (Vc D j).rank := hN ▸ i.2.2.1
  have hi1' : 1 ≤ i'.1.2 := i'.2.1
  have hi2' : i'.1.2 ≤ (Vc D j).rank := hN ▸ i'.2.2.1
  have hA := (p.R.B.L j (p.R.mu w)).hecke.hA_loc i.1 ⟨hi1, hi2⟩
  have hA' := (p.R.B.L j (p.R.mu w)).hecke.hA_loc i'.1 ⟨hi1', hi2'⟩
  by_cases hv : (plOf p j (p.R.mu w) i.1.1).under (𝓞 D.host.F) = (plOf p j (p.R.mu w) i'.1.1).under (𝓞 D.host.F)
  · exact exists_equiv_of_fibre_card (levJ p j (p.R.mu w)) (hkA p j (p.R.mu w) i.1) (hkA p j (p.R.mu w) i'.1) F.Triv
      (_root_.GlobalTheory.HeckePairCount.card_pairs_comm p j (p.R.mu w) i.1 i'.1 hi1 hi2 hi1' hi2' hv)
      (fun s hs t ht t' ht' s' hs' hK => _root_.GlobalTheory.FrameTriv.triv_of_isLocEnv p j w e0 b io ev bs rk sh Lf kap chi hc i.1 hi1 hi2 i.2.2.2 _ hK
        (_root_.GlobalTheory.FrameProdLoc.isLocEnv_prod (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i.1 i'.1 s t t' s' hv (hA s hs) (hA' t ht) (hA' t' ht') (hA s' hs')))
  · refine ⟨Equiv.prodComm _ _, fun x => ?_⟩
    have hcomm : (x.1 : F.G) * (x.2 : F.G) = (x.2 : F.G) * (x.1 : F.G) :=
      _root_.GlobalTheory.LocComm.mul_comm_of_isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok (p.R.mu w)) i.1 i'.1 (x.1 : F.G) (x.2 : F.G) hv (hA _ x.1.2) (hA' _ x.2.2)
    show F.Triv (((x.2 : F.G) * (x.1 : F.G))⁻¹ * ((x.1 : F.G) * (x.2 : F.G)))
    rw [hcomm, inv_mul_cancel]
    exact ⟨one_mem _, map_one _, map_one _⟩

end GlobalTheory.HeckeCommFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexFibreIsoUniversalGroupFramedPoint
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
noncomputable section

namespace GlobalTheory.PtDeg

open _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem fibre_iso_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ : E →+* ℂ) (v : Fin (Dw.mult ρ) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ v → ∀ (σ : K →+* ℂ) (φ : K →ₐ[c.F] CAt (σ.comp (algebraMap c.F K))), (∀ a, toC (φ a) = σ a) → ∀ (z : FrPt Xo c (CAt (σ.comp (algebraMap c.F K)))), FrMap φ y z → ∀ (Q : ReciprocityTheory.ChartRestriction.G.Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ F.P₀.A.left) (v' : Fin F.P₀.g → (epsR ℂ ⟶ Q.A)), GlobalTheory.IsPolFibre σ F.P₀ Q ψ → (∀ i, GlobalTheory.IsVecOver σ ψ (F.v i) (v' i)) → ∀ (T : GlobalTheory.CM.PAT H (Sp ℂ)) (m : SABMap T.t Xo.univ.t z.x), ∃ f : Q.A ⟶ T.pol.A, IsMonHom f ∧ LBIso (lbPow (T.pol.L.pull f.left) 1) (lbPow Q.L 1) ∧ ∀ i (q : epsR ℂ ⟶ Q.A), IsLieComb (fun k => σ (v i k)) v' q → ∀ w' : epsR ℂ ⟶ T.pol.A, w'.left ≫ m.φ = z.u ρ i → q ≫ f = w' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 F ρ v hFC σ φ hφ z hz Q ψ v' hQ hv' T m

  have hφσ : (φ.toRingHom : K →+* ℂ) = σ := RingHom.ext hφ
  have hbase : z.x = spMap σ ≫ y.x := by rw [hz.1, hφσ]; rfl

  have hcomp := hQ.2.1.comp F.fib.2.1
  have w0 : (ψ ≫ F.φ) ≫ B.t.G.hom = (Q.A.hom ≫ spMap σ) ≫ spMap (algebraMap (𝓞 K) K) := by
    rw [hcomp.1.w, Category.assoc]
  let χ₀ : Q.A.left ⟶ t₀.G.left := m2.cart.1.lift (ψ ≫ F.φ) (Q.A.hom ≫ spMap σ) w0
  have hχ₀2 : χ₀ ≫ m2.φ = ψ ≫ F.φ := m2.cart.1.lift_fst _ _ w0
  have hχ₀b : χ₀ ≫ t₀.G.hom = Q.A.hom ≫ spMap σ := m2.cart.1.lift_snd _ _ w0
  have hχ₀ : IsGrpPullback Q.A t₀.G (spMap σ) χ₀ := m2.cart.cancel (by rw [hχ₀2]; exact hcomp) hχ₀b
  have hχ := hχ₀.comp m1.cart
  have w1 : (χ₀ ≫ m1.φ) ≫ Xo.univ.t.G.hom = Q.A.hom ≫ z.x := by rw [hχ.1.w, hbase]
  let fl : Q.A.left ⟶ T.t.G.left := m.cart.1.lift (χ₀ ≫ m1.φ) Q.A.hom w1
  have hfl : fl ≫ m.φ = χ₀ ≫ m1.φ := m.cart.1.lift_fst _ _ w1
  have hflb : fl ≫ T.t.G.hom = Q.A.hom := m.cart.1.lift_snd _ _ w1
  let f : Q.A ⟶ T.pol.A := Over.homMk fl hflb
  refine ⟨f, ?_, ?_, ?_⟩
  ·
    refine GlobalTheory.DivisibleHom.isMonHom_of_mul_points f fun S x y => ?_
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · have e1 := hχ.2 S x y (pushPt hχ.1.w x) (pushPt hχ.1.w y) rfl rfl
      have e2 := m.cart.2 S (x ≫ f) (y ≫ f) (pushPt m.cart.1.w (x ≫ f)) (pushPt m.cart.1.w (y ≫ f)) rfl rfl
      rw [Over.comp_left, Category.assoc]
      change _ ≫ fl ≫ m.φ = _
      rw [hfl, ← e1, ← e2]
      refine mul_left_congr (by rw [hbase]) _ _ _ _ ?_ ?_
      · show x.left ≫ χ₀ ≫ m1.φ = (x.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
      · show y.left ≫ χ₀ ≫ m1.φ = (y.left ≫ fl) ≫ m.φ
        rw [Category.assoc, hfl]
    · exact (Over.w ((x * y) ≫ f)).trans (Over.w ((x ≫ f) * (y ≫ f))).symm
  ·
    obtain ⟨wT, hwT, -⟩ := m.lin
    obtain ⟨w1', hw1', -⟩ := m1.lin
    obtain ⟨w2', hw2', -⟩ := m2.lin
    have hT : LBIso T.t.PP.L (Xo.univ.t.PP.L.pull m.φ) := ⟨wT, hwT⟩
    have h1 : LBIso t₀.PP.L (Xo.univ.t.PP.L.pull m1.φ) := ⟨w1', hw1'⟩
    have h2 : LBIso t₀.PP.L (B.t.PP.L.pull m2.φ) := ⟨w2', hw2'⟩
    have hT2 := GlobalTheory.CM.EllComp.lbIso_pull_comp hT.symm fl
    rw [hfl] at hT2
    have h3 := GlobalTheory.CM.EllComp.lbIso_pull_comp h1.symm χ₀
    have h4 := GlobalTheory.CM.EllComp.lbIso_pull_comp h2.symm χ₀
    rw [hχ₀2] at h4
    have h5 : LBIso (B.t.PP.L.pull (ψ ≫ F.φ)) (F.P₀.L.pull ψ) := GlobalTheory.CM.EllComp.lbIso_pull_comp F.fib.2.2 ψ
    have e45 := LBIso.trans (pull_isLB B.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ) Q.isLB h5 hQ.2.2
    have e345 := LBIso.trans (pull_isLB t₀.PP.isLB χ₀) (pull_isLB B.t.PP.isLB _) Q.isLB h4.symm e45
    have e2345 := LBIso.trans (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB t₀.PP.isLB χ₀) Q.isLB h3 e345
    have main : LBIso (T.t.PP.L.pull fl) Q.L :=
      LBIso.trans (pull_isLB T.t.PP.isLB fl) (pull_isLB Xo.univ.t.PP.isLB _) Q.isLB hT2.symm e2345
    exact GlobalTheory.lbIso_lbPow main 1
  ·
    intro i q hq w' hw'
    obtain ⟨u, w, hu1, hu2, hw⟩ := hFC i
    haveI := GlobalTheory.ShFam.OpenReg.mono_spMap_algebraMap (𝓞 K) K
    have hFw : F.φ ≫ B.t.G.hom = F.P₀.A.hom ≫ spMap (algebraMap (𝓞 K) K) := F.fib.2.1.1.w
    have hu3 : u ≫ t₀.G.hom = spMap (algebraMap K (DualNumber K)) := by
      rw [← cancel_mono (spMap (algebraMap (𝓞 K) K))]
      calc (u ≫ t₀.G.hom) ≫ spMap (algebraMap (𝓞 K) K) = (u ≫ m2.φ) ≫ B.t.G.hom := by
            rw [Category.assoc, Category.assoc, m2.cart.1.w]
        _ = (w.left ≫ F.P₀.A.hom) ≫ spMap (algebraMap (𝓞 K) K) := by
            rw [hu2, Category.assoc, hFw, Category.assoc]
        _ = spMap (algebraMap K (DualNumber K)) ≫ spMap (algebraMap (𝓞 K) K) := by rw [Over.w w]; rfl
    obtain ⟨q', hq', -⟩ := GlobalTheory.existsUnique_isVecOver hQ.2.1.1 w
    have hq'c : IsLieComb (fun k => σ (v i k)) v' q' := by
      let d := ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ
      have dover : spMap d ≫ spMap (algebraMap K (DualNumber K)) =
          spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ := by
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext r <;> simp [d, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
      have dscale (a : K) : spMap d ≫ spMap (epsScaleR a) =
          spMap (epsScaleR (σ a)) ≫ spMap d := by
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext r <;> simp [d, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      rw [GlobalTheory.ArcQ.NormalForm.isLieComb_iff] at hw ⊢
      let U : Over.mk ((epsR ℂ).hom ≫ spMap σ) ⟶ epsR K := Over.homMk (spMap d) dover
      have e₁ := map_list_prod (pushHom hQ.2.1 (epsR ℂ)) (List.ofFn fun k => GlobalTheory.ArcQ.NormalForm.sc (σ (v i k)) ≫ v' k)
      have e₂ := map_list_prod (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := F.P₀.A) U) (List.ofFn fun k => GlobalTheory.ArcQ.NormalForm.sc (v i k) ≫ F.v k)
      rw [List.map_ofFn] at e₁ e₂
      have e₃ : (pushHom hQ.2.1 (epsR ℂ)) ∘ (fun k => GlobalTheory.ArcQ.NormalForm.sc (σ (v i k)) ≫ v' k) =
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.preHom (G := F.P₀.A) U) ∘ fun k => GlobalTheory.ArcQ.NormalForm.sc (v i k) ≫ F.v k :=
        funext fun k => Over.OverMorphism.ext (by
          show (spMap (epsScaleR (σ (v i k))) ≫ (v' k).left) ≫ ψ =
            spMap d ≫ spMap (epsScaleR (v i k)) ≫ (F.v k).left
          rw [Category.assoc, hv', ← Category.assoc, ← Category.assoc, dscale])
      rw [e₃, ← e₂, ← hw] at e₁
      apply Over.OverMorphism.ext
      apply hQ.2.1.1.hom_ext
      · exact hq'.trans (congrArg (·.left) e₁).symm
      · rw [Over.w, Over.w]
    have hqq : q = q' := by
      obtain ⟨a, ha, rfl⟩ := hq
      obtain ⟨b, hb, rfl⟩ := hq'c
      have hab : a = b := funext fun k => Over.OverMorphism.ext ((ha k).trans (hb k).symm)
      rw [hab]
    subst hqq
    have key : q.left ≫ χ₀ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR σ) ≫ u := by
      apply m2.cart.1.hom_ext
      · rw [Category.assoc, hχ₀2, Category.assoc, hu2, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ F.φ) hq'
      · rw [Category.assoc, hχ₀b, Category.assoc, hu3, ← Category.assoc, Over.w q]
        show spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap σ = _
        rw [GlobalTheory.spMap_comp_spMap, GlobalTheory.spMap_comp_spMap]
        congr 1
        ext a <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hw', hz.2.1, ← hu1, hφσ]
      change (q.left ≫ fl) ≫ m.φ = _
      rw [Category.assoc, hfl, ← Category.assoc, key, Category.assoc]
      rfl
    · exact (Over.w (q ≫ f)).trans (Over.w w').symm

end GlobalTheory.PtDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationLargeInertPrime
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum.InertOsc

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig IsSmall IsSpread sumSmallSpread not_isBig_iff)

theorem card_filter_inPsi {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    [DecidablePred (fun τ : E →+* ℂ => InPsi H τ)] :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = Module.finrank ℚ E / 2 := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact GlobalTheory.LamF.card_psiSet H

theorem nuBetween_mono {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {p : ℕ} [Fact p.Prime] {la : PointsOfFlagModel.abelian₂ p c}
    {cx : Lt1 Dw → ℕ} {A B B' : ℝ} (h : NuBetween Xo la cx A B) (hB : B ≤ B') : NuBetween Xo la cx A B' :=
  fun T io e ho y => ⟨(h T io e ho y).1, fun ha => ((h T io e ho y).2 ha).trans (EReal.coe_le_coe_iff.2 hB)⟩

theorem big_arith {i q k m p : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    2 * i + 2 * q * p ≤ 5 * m * p := by
  have h1 : 2 * m ≤ m * p := by nlinarith
  have h2 : q * p ≤ m * p := Nat.mul_le_mul_right _ hq
  nlinarith

theorem big_bound {i q k m p c : ℕ} (hi : i + 1 ≤ k + m) (hk : k ≤ m * p) (hq : q ≤ m) (hp : 2 ≤ p) :
    boundInert p q i c ≤ 5 * (m : ℝ) * c / ((p : ℝ) - 1) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hn : ((2 * i + 2 * q * p : ℕ) : ℝ) ≤ ((5 * m * p : ℕ) : ℝ) := by exact_mod_cast big_arith hi hk hq hp
  push_cast at hn
  unfold boundInert
  rw [div_add_div _ _ (by positivity) hp1.ne', div_le_div_iff₀ (by positivity) hp1]
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have : (2 * (i : ℝ) * c * ((p : ℝ) - 1) + (p * ((p : ℝ) - 1)) * (2 * q * c)) * ((p : ℝ) - 1)
      = ((2 * i + 2 * q * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  have : 5 * (m : ℝ) * c * (p * ((p : ℝ) - 1) * ((p : ℝ) - 1)) = ((5 * m * p) * c) * ((p : ℝ) - 1) ^ 2 := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn hc) (sq_nonneg _)

theorem rk_add_one_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (f : Lt1 Dw) : rk f + 1 ≤ Dw.p + Dw.q + 1 := by
  have h := rk_le f
  unfold Datum.mult at h
  split_ifs at h <;> omega

theorem oscLe_inert_large : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], ¬ (p : ℤ) ∣ discr E → InertInK H p → k ≤ m * p → OscLe Xo c p cx ((6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1) := by
  classical
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _ hdisc hin hkp
  obtain ⟨hS1, hSq, hmk, hm1, hk2, hF⟩ := hS
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    linarith
  intro la
  set w : Lt1 Dw → ℝ := fun f => if IsBig k f then 5 * (m : ℝ) * cx f / ((p : ℝ) - 1)
    else (rk f : ℝ) * cx f / ((p : ℝ) - 1) with hw
  have key : ∀ f, ∃ ab : ℝ × ℝ, FacBetween Xo la f (cx f) ab.1 ab.2 ∧ ab.2 - ab.1 ≤ w f := by
    intro f
    by_cases hb : IsBig k f
    · obtain ⟨A, B, hAB, hBA⟩ := _root_.GlobalTheory.RefSum.facBetween_inert E H Dw l Xo c p la hdisc hin f (cx f) hb.1
      refine ⟨(A, B), hAB, ?_⟩
      simp only [hw, if_pos hb]
      exact hBA.trans (big_bound (by have := rk_add_one_le f; omega) hkp hSq hp2)
    · refine ⟨(0, boundAll p (rk f) (cx f)), (_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).1, ?_⟩
      simp only [hw, if_neg hb, boundAll, sub_zero, le_refl]
  choose g hg using key
  obtain ⟨n, hn⟩ := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun f => (g f).1) (fun f => (g f).2) fun f => (hg f).1).2
  refine ⟨n, nuBetween_mono hn ?_⟩
  have hsum : ∑ f, ((g f).2 - (g f).1) ≤ ∑ f, w f := Finset.sum_le_sum fun f _ => (hg f).2
  suffices hw2 : ∑ f, w f ≤ (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) by linarith

  have hcard : (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
    rw [card_filter_inPsi H, hF]; omega
  have hB : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ F * Mb := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun f : Lt1 Dw => IsBig k f))
      (t := Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)) (g := fun f : Lt1 Dw => f.1)
      (fun f hf => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢; exact hf.1)]
    calc _ ≤ ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ), Mb := by
          refine Finset.sum_le_sum fun τ _ => ?_
          have h := hbig τ
          push_cast at h
          rw [Finset.filter_filter]
          convert h using 2
      _ = F * Mb := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  have hSS : ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => ¬ IsBig k f), (rk f : ℝ) * cx f = (sumSmallSpread k cx : ℝ) := by
    unfold sumSmallSpread
    push_cast
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_isBig_iff]
  simp only [hw]
  rw [Finset.sum_ite, ← Finset.sum_div, ← Finset.sum_div, ← add_div, ← Finset.mul_sum, hSS]
  refine div_le_div_of_nonneg_right ?_ hp1.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h5 : 5 * (m : ℝ) * ∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f), (cx f : ℝ) ≤ 5 * m * (F * Mb) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h6 : 5 * (m : ℝ) * (F * Mb) ≤ 6 * F * m * Mb := by
    have : (0 : ℝ) ≤ F * m * Mb := by positivity
    nlinarith
  linarith

end GlobalTheory.RefSum.InertOsc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DepthOscillationZeroAboveAndDegreeBound
section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread not_isBig_iff)


open Classical in
theorem card_filter_inPsi_of_finrank {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {F : ℕ} (hF : Module.finrank ℚ E = 2 * F) :
    (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card = F := by
  have h := GlobalTheory.LamF.card_psiSet H
  rw [hF] at h
  have h2 : Nat.card (GlobalTheory.LamF.psiSet H) = (Finset.univ.filter (fun τ : E →+* ℂ => InPsi H τ)).card := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
    rfl
  omega


open Classical in
theorem degree_le_of_exponentBound {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {F k m M : ℕ} {Mb Sm : ℝ} {cx : Lt1 Dw → ℕ} (hS : Shape Dw F k m) (hE : ExpBd Dw k cx Mb Sm M) :
    (∑ f : Lt1 Dw, (rk f : ℝ) * (cx f : ℝ)) ≤ F * (Dw.p + Dw.q : ℕ) * Mb + Sm := by
  obtain ⟨hMb, hbig, hsm, -⟩ := hE
  have hF : Module.finrank ℚ E = 2 * F := hS.2.2.2.2.2
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (IsBig k)]
  refine add_le_add ?_ ?_
  · have hB : ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) ≤ F * Mb := by
      rw [← Finset.sum_fiberwise (Finset.univ.filter (IsBig k)) (fun f : Lt1 Dw => f.1)]
      calc ∑ τ : E →+* ℂ, ∑ f ∈ (Finset.univ.filter (IsBig k)).filter (fun f : Lt1 Dw => f.1 = τ), (cx f : ℝ)
          ≤ ∑ τ : E →+* ℂ, if InPsi H τ then Mb else 0 := by
            refine Finset.sum_le_sum fun τ _ => ?_
            split_ifs with hτ
            · have := hbig τ
              rw [Finset.filter_filter]
              push_cast at this
              convert this using 3
            · apply le_of_eq
              apply Finset.sum_eq_zero
              intro f hf
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
              exact absurd (hf.2 ▸ hf.1.1) hτ
        _ = F * Mb := by
            rw [← Finset.sum_filter, Finset.sum_const, card_filter_inPsi_of_finrank H hF, nsmul_eq_mul]
    have hN : ∀ f : Lt1 Dw, (rk f : ℝ) ≤ ((Dw.p + Dw.q : ℕ) : ℝ) := by
      intro f
      have h1 := rk_le f
      have h2 : Dw.mult f.1 ≤ Dw.p + Dw.q := by
        unfold Datum.mult; split_ifs <;> omega
      exact_mod_cast h1.trans h2
    calc ∑ f ∈ Finset.univ.filter (IsBig k), (rk f : ℝ) * (cx f : ℝ)
        ≤ ∑ f ∈ Finset.univ.filter (IsBig k), ((Dw.p + Dw.q : ℕ) : ℝ) * (cx f : ℝ) :=
          Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hN f) (Nat.cast_nonneg _)
      _ = ((Dw.p + Dw.q : ℕ) : ℝ) * ∑ f ∈ Finset.univ.filter (IsBig k), (cx f : ℝ) := by rw [Finset.mul_sum]
      _ ≤ ((Dw.p + Dw.q : ℕ) : ℝ) * (F * Mb) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = F * (Dw.p + Dw.q : ℕ) * Mb := by ring
  · have he : ∑ f ∈ Finset.univ.filter (fun f => ¬ IsBig k f), (rk f : ℝ) * (cx f : ℝ) = (sumSmallSpread k cx : ℝ) := by
      unfold sumSmallSpread
      push_cast
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext f
      simp [not_isBig_iff]
    rw [he]; exact hsm

theorem oscLe_zero_above_and_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (F k m M : ℕ) (Mb Sm : ℝ) (cx : Lt1 Dw → ℕ), Shape Dw F k m → ExpBd Dw k cx Mb Sm M → ∀ (p : ℕ) [Fact p.Prime], (M < p → OscLe Xo c p cx 0) ∧ OscLe Xo c p cx ((F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1)) := by
  intro E _ _ _ H Dw l Xo c F k m M Mb Sm cx hS hE p _
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  constructor
  · intro hMp la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun _ => 0)
      (fun f => (_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).2 (lt_of_le_of_lt (hE.2.2.2 f) hMp))).1
    simpa using h
  · intro la
    refine ⟨0, ?_⟩
    have h := ((GlobalTheory.T.productDepth_sum_rounding_oscillation E H Dw l Xo c p la cx).1 (fun _ => 0) (fun f => boundAll p (rk f) (cx f))
      (fun f => (_root_.GlobalTheory.RefSum.facBetween_zero_boundAll E H Dw l Xo c p la f (cx f)).1)).1
    have hsum : ∑ f, boundAll p (rk f) (cx f) ≤ (F * (Dw.p + Dw.q : ℕ) * Mb + Sm) / ((p : ℝ) - 1) := by
      unfold boundAll
      rw [← Finset.sum_div]
      exact div_le_div_of_nonneg_right (degree_le_of_exponentBound hS hE) (by linarith)
    intro T io e ho y
    obtain ⟨h1, h2⟩ := h T io e ho y
    refine ⟨by simpa using h1, fun ha => (h2 ha).trans ?_⟩
    simp only [Finset.sum_const_zero, Nat.cast_zero, zero_add]
    exact EReal.coe_le_coe_iff.2 hsum

end GlobalTheory.RefSum
end
end

