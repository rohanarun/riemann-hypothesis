module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0065
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0743
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.HeckePointLaw

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeBorelChange

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (hψ : IsLinHom ψ) {p m : ℕ}
    {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsLieImg p ψ (v j) (v' j))
    (cf : Fin m → Ω) {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (htw : IsTanAt x w) (htw' : IsTanAt x' w')
    (hw : IsCombAt x v cf w) (hw' : IsCombAt x' v' cf w') : IsLieImg p ψ w w' := by
  let A : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (v j) (hv j).1.1
  let B : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun j => Over.homMk (v' j) (hv j).2.1.1
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w htw.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' htw'.1
  have hAB : ∀ j, scaleAt x' (p : Ω) ≫ B j = tanMap hψ (A j) := fun j => by
    obtain ⟨-, -, a, ha, e⟩ := hv j
    have : a = A j := Over.OverMorphism.ext ha
    subst this
    exact Over.OverMorphism.ext e
  have hW : (List.ofFn fun i => scaleAt x (cf i) ≫ A i).prod = W := (isCombAt_iff A cf W).1 hw
  have hW' : (List.ofFn fun i => scaleAt x' (cf i) ≫ B i).prod = W' := (isCombAt_iff B cf W').1 hw'
  let Lc : (tEps x' ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' (p : Ω) ≫ b) fun b b' => MonObj.comp_mul _ _ _
  have key : scaleAt x' (p : Ω) ≫ W' = tanMap hψ W := by
    have e1 : scaleAt x' (p : Ω) ≫ W' = Lc W' := rfl
    rw [e1, ← hW, ← hW', map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    simp only [Function.comp_apply, Lc, MonoidHom.mk'_apply]
    rw [tanMap_scale, ← hAB, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  exact ⟨htw, htw', W, rfl, congrArg (·.left) key⟩

theorem scal_mul'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem secBC_self {Ω : Type} [CommRing Ω] {x : Sp Ω ⟶ Xo.X} {a : Ω} {s s' : LB.Sec (PPx x)}
    (h : GlobalTheory.Frames.SecBC (RingHom.id Ω) a x x s s') : ∀ i, s'.f i = scal x a i * s.f i := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := h
  have e0 : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (by rw [e0]; simp))
    (h₁.trans (Category.id_comp _).symm)
  intro i
  have e : Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

end SlopeTestRemainingChoices

theorem hkRelFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  intro E _ _ _ H Dw l Xo c P p i hP Ω _ _ _ t w z hb C z' hz
  have hsp : IsSplitOff l P p := hP
  obtain ⟨g, hg0, hgd, hgc⟩ := (GlobalTheory.Frames.frBor_iff_frChg w z t).1 hb
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
    GlobalTheory.Frames.lowerTri_isUnit_det _ (hg0 τ) fun j => by rw [hgd]; exact Units.isUnit _
  have hdet' : ∀ τ, IsUnit ((g τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (hdet τ).ringInverse
  obtain ⟨w', hw', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c Ω z' (fun τ => (g τ)⁻¹) (t none)⁻¹ hdet'
  have hdiag : ∀ τ j, (g τ)⁻¹ j j = ((t⁻¹ (some ⟨τ, j⟩) : Ωˣ) : Ω) := fun τ j => by
    have e := GlobalTheory.Frames.lowerTri_mul_diag ((g τ)⁻¹) (g τ) (GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ)) (hg0 τ) j
    rw [Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_apply_eq, hgd] at e
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left e.symm
  have hb' : FrBor t⁻¹ z' w' := (GlobalTheory.Frames.frBor_iff_frChg z' w' t⁻¹).2
    ⟨fun τ => (g τ)⁻¹, fun τ => GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ), hdiag, hw'⟩
  have hbw : FrBor t w' z' := by
    simpa using (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c Ω z' w' w').2.2.2 t⁻¹ hb'
  obtain ⟨ψ, hiso, hlie, hth⟩ := (hkPt_iff hsp _ z C.1 z').1 hz
  obtain ⟨hx, hc, hs⟩ := hgc
  obtain ⟨hx', hc', hs'⟩ := hw'
  obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z
  dsimp only at hx
  subst hx
  obtain ⟨zx', zo', zu', ztan', zeig', zbas', zs', zgen'⟩ := z'
  dsimp only at hx'
  subst hx'
  refine ⟨C, w', (hkPt_iff hsp _ w C.1 w').2 ⟨ψ, hiso, fun τ j => ?_, ?_⟩, hbw⟩
  · have hcomb : IsCombAt w.x (zu τ) ((g τ)⁻¹ j) (w.u τ j) := by
      obtain ⟨a, ha, -⟩ := zbas τ (w.u τ j) (w.tan τ j) (w.eig τ j)
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo Ω w.x (w.u τ) (w.tan τ) (zu τ) (g τ).transpose a
        (w.u τ j) (fun k => hc τ k) ha
      have h2 := Formalism.L2.PjFree.isCombAt_single (w.tan τ) j
      have e : (g τ).transpose.mulVec a = Pi.single j 1 :=
        (w.basis τ (w.u τ j) (w.tan τ j) (w.eig τ j)).unique h1 h2
      have ea : a = (g τ)⁻¹ j := by
        have e2 := congrArg ((g τ).transpose⁻¹.mulVec) e
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hdet τ),
          Matrix.one_mulVec, Matrix.mulVec_single_one] at e2
        rw [e2, ← Matrix.transpose_nonsing_inv]
        ext k
        rfl
      exact ea ▸ ha
    exact isLieImg_comb hiso.2.1 (fun k => hlie τ k) ((g τ)⁻¹ j) (w.tan τ j) (w'.tan τ j) hcomb (hc' τ j)
  · have hth' : GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP ψ p zs zs' := by
      have := hth
      simp only [GlobalTheory.ThetaTrace.hkTr, Equiv.apply_symm_apply] at this
      exact this
    show GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj w.x w'.x ((conj w.x w'.x).symm ψ)) p w.s w'.s
    rw [Equiv.apply_symm_apply]
    have hs₁ := secBC_self hs
    have hs₂ := secBC_self hs'
    refine GlobalTheory.ThetaTrace.IsThetaTrace.smul hth' (toΓ Ω (((t none)⁻¹ : Ωˣ) : Ω)) (fun k => ?_) (fun k => hs₂ k)
    show w.s.f k = scal w.x (((t none)⁻¹ : Ωˣ) : Ω) k * zs.f k
    rw [hs₁ k, ← _root_.mul_assoc, ← scal_mul'', Units.inv_mul, scal_one'', _root_.one_mul]

end GlobalTheory.HeckeBorelChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

theorem isLocalArtin_transport : GlobalArtinReciprocity → ChevalleyUnits → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∀ (a : Weil h →* (w.adicCompletion E)ˣ) (a' : Weil h' →* (w'.adicCompletion E')ˣ), IsLocalArtin h a → IsLocalArtin h' a' → ∀ σ σ', WeilRel φ σ σ' → a' σ' = Units.map i.toRingHom.toMonoidHom (a σ) := by
  intro hG hC E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP a a' ha ha' σ σ' hσ
  obtain ⟨art, hart⟩ := hG E Ω
  obtain ⟨art', hart'⟩ := hG E' Ω'
  let x : (w.adicCompletion E)ˣ := Units.map i.symm.toRingHom.toMonoidHom (a' σ')
  have hx : Units.map i.toRingHom.toMonoidHom x = a' σ' := by
    ext
    simp [x]
  have h1 := _root_.GlobalTheory.LocDegOne.artin_of_placeIso E Ω A w h E' Ω' A' w' h' φ j i hP art art' hart hart' σ σ' x hσ
    (by rw [hx]; exact ha'.glob art' hart' σ')
  have h2 : x = a σ := _root_.GlobalTheory.ArtinLocalInj.artin_localIdele_injective hC E Ω art hart w (h1.trans (ha.glob art hart σ).symm)
  rw [← hx, h2]

end GlobalTheory.LocLanglands
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie

noncomputable section
namespace GlobalTheory.HeckeCount
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pLat (D : Datum H) (p : ℕ) : AddSubgroup D.La := (DistribSMul.toAddMonoidHom D.La p).range

theorem mem_pLat {D : Datum H} {p : ℕ} {a : D.La} : a ∈ pLat D p ↔ ∃ b, a = p • b := by
  simp [pLat, eq_comm]

def LatCount (D : Datum H) (p : ℕ) (J : Ideal (𝓞 E)) (m : ℕ) : Type :=
  {N : AddSubgroup D.La // pLat D p ≤ N ∧ (∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) ∧
    (∀ a ∈ J, ∀ x ∈ N, a • x ∈ pLat D p) ∧ (pLat D p).relIndex N = m}

section Alg
variable {D : Datum H} {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)

def evA (p : ℕ) : D.La →+ Additive Q :=
  AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev p a)) fun a b => by rw [I.add]; rfl

theorem ker_evA {p : ℕ} (hp : 0 < p) : (evA I p).ker = pLat D p := by
  ext a
  rw [AddMonoidHom.mem_ker, mem_pLat, ← I.ker p hp a]
  exact ofMul_eq_zero

theorem relIndex_eq {p : ℕ} (hp : 0 < p) (N : AddSubgroup D.La) :
    (pLat D p).relIndex N = Nat.card (N.map (evA I p)) := by
  rw [← ker_evA I hp, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddMonoidHom.comap_ker,
    AddSubgroup.index_ker, AddMonoidHom.range_comp, AddSubgroup.range_subtype]

end Alg
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
section Alg2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {k : Type} [Field k] {Q : Type} [CommGroup Q] {act : 𝓞 E → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e)

theorem card_toAdd (C : Subgroup Q) : Nat.card C.toAddSubgroup = Nat.card C :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun _ => Iff.rfl)

def datumEquiv {p : ℕ} (hp : 0 < p) (hnat : ∀ x, act (p : 𝓞 E) x = x ^ p) {J : Ideal (𝓞 E)}
    (hpJ : (p : 𝓞 E) ∈ J) {m : ℕ} (hm : m ≠ 0) :
    {C₀ : Subgroup Q // (∀ a, ∀ x ∈ C₀, act a x ∈ C₀) ∧ (∀ x ∈ C₀, ∀ a ∈ J, act a x = 1) ∧ Finite C₀ ∧
      Nat.card C₀ = m} ≃ LatCount D p J m where
  toFun C := ⟨C.1.toAddSubgroup.comap (evA I p), by
      rw [← ker_evA I hp]; exact AddMonoidHom.ker_le_comap _ _,
    fun a x hx => by
      show (I.ev p (a • x)) ∈ C.1
      rw [I.lin]; exact C.2.1 a _ hx,
    fun a ha x hx => by
      rw [← ker_evA I hp, AddMonoidHom.mem_ker]
      show Additive.ofMul (I.ev p (a • x)) = 0
      rw [I.lin, show act a (I.ev p x) = 1 from C.2.2.1 _ hx a ha]; rfl,
    by
      have hle : C.1.toAddSubgroup ≤ (evA I p).range := fun x hx => by
        have h1 : x.toMul ^ p = 1 := (hnat _).symm.trans (C.2.2.1 _ hx _ hpJ)
        obtain ⟨a, ha⟩ := (I.onto p hp _).1 h1
        exact ⟨a, ha⟩
      rw [relIndex_eq I hp, AddSubgroup.map_comap_eq, inf_eq_right.2 hle, card_toAdd]
      exact C.2.2.2.2⟩
  invFun N := ⟨Subgroup.toAddSubgroup.symm (N.1.map (evA I p)), by
      rintro a _ ⟨x, hx, rfl⟩
      exact ⟨a • x, N.2.2.1 a x hx, I.lin p a x⟩,
    by
      rintro _ ⟨x, hx, rfl⟩ a ha
      have h := N.2.2.2.1 a ha x hx
      rw [← ker_evA I hp, AddMonoidHom.mem_ker] at h
      show act a (I.ev p x) = 1
      rw [← I.lin]; exact h,
    by
      have : Nat.card (Subgroup.toAddSubgroup.symm (N.1.map (evA I p))) ≠ 0 := by
        rw [← card_toAdd, OrderIso.apply_symm_apply, ← relIndex_eq I hp, N.2.2.2.2]; exact hm
      exact Nat.finite_of_card_ne_zero this,
    by rw [← card_toAdd, OrderIso.apply_symm_apply, ← relIndex_eq I hp]; exact N.2.2.2.2⟩
  left_inv C := by
    apply Subtype.ext
    show Subgroup.toAddSubgroup.symm _ = C.1
    rw [AddSubgroup.map_comap_eq, OrderIso.symm_apply_eq]
    refine inf_eq_right.2 fun x hx => ?_
    have h1 : x.toMul ^ p = 1 := (hnat _).symm.trans (C.2.2.1 _ hx _ hpJ)
    obtain ⟨a, ha⟩ := (I.onto p hp _).1 h1
    exact ⟨a, ha⟩
  right_inv N := by
    apply Subtype.ext
    show AddSubgroup.comap (evA I p) (Subgroup.toAddSubgroup (Subgroup.toAddSubgroup.symm (N.1.map (evA I p)))) = N.1
    rw [OrderIso.apply_symm_apply, AddSubgroup.comap_map_eq, ker_evA I hp]
    exact sup_eq_left.2 N.2.1

end Alg2
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

section Fibre
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
  [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}


include hL in
theorem map_pow_eq (h : IsSplitPrimeOff l p P) {i : ℕ} {C : Subgroup (Pts o.t)}
    (hC : o.t.HeckeKer (𝟙_ _) D P p i C) {C₀ : Subgroup (Pts o.t)} (h₀ : IsHeckeDatum o.t P i C₀)
    (e : (C : Set (Pts o.t)) = heckeKernel o.t p P C₀) : C.map (powMonoidHom p) = C₀ := by
  have hcard : Nat.card (C.map (powMonoidHom p)) = Ideal.absNorm P ^ i := by
    obtain ⟨-, -, -, -, c₅, c₆⟩ := hC
    obtain ⟨-, -, hp, -, -⟩ := (splitPrime_iff l p P).1 h
    obtain ⟨-, -, hc⟩ := tate_facts hL o
    have hpos := pow_pos hp.pos (2 * (Module.finrank ℚ E / 2 * (D.p + D.q)))
    have hm := card_eq_tors_mul C p
    rw [card_tors, card_inter_tors, hc p hp.pos] at c₆
    rw [c₅] at hm
    have h₁ := mul_ne_zero_iff.1 (hm ▸ hpos.ne')
    exact mul_left_cancel₀ h₁.1 (hm.symm.trans c₆)
  have : Finite C₀ := h₀.2.2.1
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [hcard, h₀.2.2.2])
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ heckeKernel o.t p P C₀ := e ▸ hx
  obtain ⟨x₁, x₂, x₃, rfl, ⟨t₁, -⟩, ⟨-, k₂⟩, ⟨t₃, -⟩⟩ := hx'
  show (x₁ * x₂ * x₃) ^ p ∈ C₀
  rw [mul_pow, mul_pow, t₁, t₃, _root_.one_mul, _root_.mul_one]
  exact k₂

include hL in
theorem isHeckeDatum_map_pow (h : IsSplitPrimeOff l p P) {i : ℕ} {C : Subgroup (Pts o.t)}
    (hC : o.t.HeckeKer (𝟙_ _) D P p i C) : IsHeckeDatum o.t P i (C.map (powMonoidHom p)) := by
  obtain ⟨C₀, h₀, e⟩ := (heckeKer_iff hL o h i C).1 hC
  rw [map_pow_eq hL o h hC h₀ e]
  exact h₀

def heckeKerEquivDatum (h : IsSplitPrimeOff l p P) (i : ℕ) :
    {C : Subgroup (Pts o.t) // o.t.HeckeKer (𝟙_ _) D P p i C} ≃
      {C₀ : Subgroup (Pts o.t) // IsHeckeDatum o.t P i C₀} where
  toFun C := ⟨C.1.map (powMonoidHom p), isHeckeDatum_map_pow hL o h C.2⟩
  invFun C₀ := ⟨(exists_heckeKer_of_datum hL o h C₀.2).choose,
    (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.2⟩
  left_inv C := by
    apply Subtype.ext
    apply SetLike.coe_injective
    obtain ⟨C₀, h₀, e⟩ := (heckeKer_iff hL o h i C.1).1 C.2
    have hm := map_pow_eq hL o h C.2 h₀ e
    refine (exists_heckeKer_of_datum hL o h (isHeckeDatum_map_pow hL o h C.2)).choose_spec.1.trans ?_
    simp only [hm]
    exact e.symm
  right_inv C₀ := by
    apply Subtype.ext
    exact map_pow_eq hL o h (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.2 C₀.2
      (exists_heckeKer_of_datum hL o h C₀.2).choose_spec.1

end Fibre
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

section Fibre2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {k : Type} [Field k] {s : Sp k ⟶ Sp B}
  [IsAlgClosed k] [CharZero k] (hL : Out.Laws) (o : Obj D l b s) {p : ℕ} {P : Ideal (𝓞 E)}

include hL in
theorem nonempty_datum_equiv (h : IsSplitPrimeOff l p P) (i : ℕ) :
    Nonempty ({C₀ : Subgroup (Pts o.t) // IsHeckeDatum o.t P i C₀} ≃
      LatCount D p (conjIdeal H P) (Ideal.absNorm P ^ i)) := by
  obtain ⟨hP, -, hp, hpP, -⟩ := (splitPrime_iff l p P).1 h
  obtain ⟨⟨I⟩, -, -⟩ := tate_facts hL o
  have h0 : Ideal.absNorm P ≠ 0 := fun e => by
    rw [Ideal.absNorm_eq_zero_iff.1 e] at hpP
    exact Nat.cast_ne_zero.2 hp.pos.ne' (Ideal.mem_bot.1 hpP)
  exact ⟨(Equiv.subtypeEquivRight fun C₀ => Iff.rfl).trans
    (datumEquiv I hp.pos (fun x => (isAct_ptAct o.t _).nat p x) (natCast_mem_conj hpP) (pow_ne_zero i h0))⟩

end Fibre2

section Transfer2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
variable {B : Type} [CommRing B] {b : Base l B} {X : Scheme.{0}} {sX : X ⟶ Sp B} {k : Type} [Field k]
  {s : Sp k ⟶ Sp B}

theorem nonempty_transfer_equiv (u : Obj D l b sX) {o : Obj D l b s} {y : Sp k ⟶ X} (m : ObjMap o u y)
    (P : Ideal (𝓞 E)) (p i : ℕ) :
    Nonempty ({C' : Subgroup (Pts o.t) // o.t.HeckeKer (𝟙_ _) D P p i C'} ≃
      {C : Subgroup (Over.mk y ⟶ u.t.G) // u.t.HeckeKer (Over.mk y) D P p i C}) := by
  obtain ⟨ρ, -, e₀, -⟩ := exists_fibre_equiv u m
  have hx : ∀ (x : Pts o.t) (x₀ : Over.mk y ⟶ u.t.G), x₀.left = x.left ≫ m.cm.F → x₀ = ρ x := fun x x₀ h =>
    Over.OverMorphism.ext (h.trans (e₀ x).symm)
  have same : ∀ C : Subgroup (Over.mk y ⟶ u.t.G), SamePoints m (C.comap ρ.toMonoidHom : Set (Pts o.t)) C :=
    fun C x x₀ h => by rw [hx x x₀ h]; rfl
  refine ⟨{ toFun := fun C' => ⟨C'.1.map ρ.toMonoidHom, ?_⟩
            invFun := fun C => ⟨C.1.comap ρ.toMonoidHom, (heckeKer_transfer m (same C.1) P p i).1 C.2⟩
            left_inv := fun C' => Subtype.ext (Subgroup.comap_map_eq_self_of_injective ρ.injective _)
            right_inv := fun C => Subtype.ext (Subgroup.map_comap_eq_self_of_surjective ρ.surjective _) }⟩
  refine (heckeKer_transfer m (same _) P p i).2 ?_
  rw [Subgroup.comap_map_eq_self_of_injective ρ.injective]
  exact C'.2

end Transfer2
end GlobalTheory.HeckeCount

namespace GlobalTheory.HeckeCount
open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G GlobalTheory.IndefiniteRowSideFullHecke.HeckeIsogenyKernels GlobalTheory.HeckeCompare

theorem card_hkKer_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (q i : ℕ),
    GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P q → ∃ n : ℕ, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω]
      (z : FrPt Xo c Ω), Nonempty (Fin n ≃ hkKer (Xo := Xo) P q i Ω z) := by
  intro E _ _ _ H Dw l Xo c P q i hP
  refine ⟨Nat.card (LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)), fun Ω _ _ _ z => ?_⟩
  have hs : IsSplitPrimeOff l q P := (splitPrime_iff l q P).2 (GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.1 hP)
  have : CharZero Ω := charZero_of_injective_ringHom (Spec.preimage (z.x ≫ Xo.s)).hom.injective
  obtain ⟨o, ⟨m⟩⟩ := exists_fibre_obj Xo z.x z.x rfl
  obtain ⟨eT⟩ := nonempty_transfer_equiv Xo.univ m P q i
  obtain ⟨eL⟩ := nonempty_datum_equiv GlobalTheory.firstFiveLaws.1 o hs i
  let e : hkKer (Xo := Xo) P q i Ω z ≃ LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i) :=
    eT.symm.trans ((heckeKerEquivDatum GlobalTheory.firstFiveLaws.1 o hs i).trans eL)
  have : Finite (hkKer (Xo := Xo) P q i Ω z) :=
    GlobalTheory.HeckePointLaw.finite_heckeKer hs.1.pos hs.2.2.1 i z.x
  have : Finite (LatCount Dw q (conjIdeal H P) (Ideal.absNorm P ^ i)) := Finite.of_equiv _ e
  exact ⟨(Finite.equivFin _).symm.trans e.symm⟩

end GlobalTheory.HeckeCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalSatakeEqLanglandsQuotientUnramifiedStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_satake_eq_langlandsQuotient_unramified : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ZelevinskyPolynomialRing → GeometricLemma → BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (α : Fin x.1 → ℂˣ), HasSatake x.rep α → IsL (Finset.univ.val.map fun i => Segment.single (IrrGL.ofChar (GlobalTheory.SmGL.unrChar k (α i)) (isSmoothChar_of_isUnram (isUnram_unrChar k (α i)))) (IrrGL.isCusp_ofChar _ _)) x.rep := by
  first | exact @GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | exact GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar | (intros; apply GlobalTheory.LocLanglands.SatakeL.isL_single_unrChar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.TermInvProof

theorem termInv : ∀ D : D7, TermInv D := by
  intro D ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS Y s I hI hY n hn f₁ f₂ hf₁ hf₂
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.MixModel.exists_isCovolOne (D := D) (m := s) (n := V.rank)
  exact _root_.GlobalTheory.LagMeans.lagTerm_eq_of_means D ψ hS.weil.std V W μ 𝓕 hS.covol Y (fr Y) (hS.frame Y) s I hI hY ν 𝓨 hν _ _ f₂
    (hS.weil.om_pres _ f₁ hf₁) hf₁ hf₂
    (fun x hx => _root_.GlobalTheory.TargetUnipMean.mean_unip D ψ V W χV χW om hS.weil s I hI ν 𝓨 hν n hn f₁ hf₁ x hx)

end GlobalTheory.TermInvProof

end
end

