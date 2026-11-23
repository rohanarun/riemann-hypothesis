module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0143
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSubgroupsClosedNormalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
section
open AlgebraicGeometry NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
  Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameConst

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {k : U.Comp} {x : (U.X k).dom}


set_option maxHeartbeats 1000000 in
theorem exists_genReads_of_unitAt (hσ : GoodEmb c σ) (hU : IsUnf U) (h1 : 1 ≤ r) (Wt : UnfAt U k x) (Y : UnitAt Wt) :
    ∃ (bas : (Fin Wt.g ⊕ Fin Wt.g → ℤ) ≃ₗ[ℤ] (U.X k).Λ) (idx : Fin Wt.g ≃ (U.X k).Ψ × Fin r),
      IsSympl (U.X k) bas ∧ IdxIs c σ (U.X k) idx Wt.e ∧ GenReads U k bas idx Wt.e x Y.θ ∧
        ∀ z w, hermForm Y.Hm z w = hx (U.X k) bas idx x.1 z w := by
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hU' : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj U) := hU
  obtain ⟨W0⟩ := nonempty_uw hU'
  obtain ⟨hκ, hsd, -⟩ := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ _ hσ hU' h1 W0 k
  have hκ : (U.X k).κ0 = 2 * (U.X k).ξ0 := hκ
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) 0 := ⟨fun _ => antitone_const, by simp⟩
  obtain ⟨Dc, hDe, -⟩ := GlobalTheory.Dict.exists_dic E H Dw l c σ _ Wt.g 0 (U.X k) (fun _ => 0) Wt.e hσ hU.1
    (hU.2.1 k).1 (hU.2.1 k).2 hsd hdom
  have hper : ∀ x v j, pv (U.X k) Dc.idx x v j = perFr (U.X k) x v (relab c σ (Wt.e j).1) (Wt.e j).2 := fun x v j => by
    rw [Dc.per_eq, hDe]
    rfl
  have hty : ∀ j, rowType (U.X k) (Dc.idx j) = relab c σ (Wt.e j).1 := fun j => by
    rw [Dc.ty_eq, hDe]
    rfl
  have hb := Dc.sympl
  generalize Dc.bas = bas at hb
  generalize Dc.idx = idx at hper hty
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := GlobalTheory.Dict.hx_laws E r (U.X k) Wt.g bas idx 0 hb (by simp) x.1 x.2
  obtain ⟨ex, hl, e1, e2, e3, e4, -⟩ := exists_ex_transport Wt.F (Wt.ik k) Wt.Pm Wt.per
    (unC (Formalism.L2.PjFree.Unf.ofPj U) k x).x Wt.pt
  have hpv : ∀ a, Wt.Pm a = pv (U.X k) idx x.1 (Wt.φ k a : Fin r → E) := fun a => by
    funext j
    rw [Wt.pm_eq, hper]
  have hsurj : ∀ v ∈ (U.X k).Λ, ∃ a, (Wt.φ k a : Fin r → E) = v := fun v hv =>
    ⟨(Wt.φ k).symm ⟨v, hv⟩, by simp⟩
  have hrange : ∀ z, z ∈ Wt.Pm.range ↔ ∃ v ∈ (U.X k).Λ, z = pv (U.X k) idx x.1 v := fun z => by
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨_, (Wt.φ k a).2, hpv a⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj v hv
      exact ⟨a, hpv a⟩
  have hEF : ∀ a b, (((Wt.F.Di (Wt.ik k)).EF a b : ℤ) : ℚ) = EF (U.X k) (Wt.φ k a : Fin r → E) (Wt.φ k b) := by
    intro a b
    rw [Wt.isom, EF_def, hκ]
    congr 1; ring
  have hhx : ∀ z w, hermForm Y.Hm z w = hx (U.X k) bas idx x.1 z w := by
    refine (huniq _ (U.X k).Λ_span).2 Y.Hm Y.herm ?_
    intro u hu v hv
    obtain ⟨a, rfl⟩ := hsurj u hu
    obtain ⟨b, rfl⟩ := hsurj v hv
    rw [← hpv, ← hpv, Y.c1, ← hEF]
    simp
  have hl' : (fun z => (ex z).left) = fun z => (Wt.F.ex (Wt.ik k) Wt.Pm z).left := funext hl
  refine ⟨bas, idx, hb, ⟨hper, hty⟩,
         ⟨{ ex := ex
            ex_add := e1
            ex_onto := e2
            ex_ker := fun z => (e3 z).trans (hrange z)
            ex_lin := fun a z => by simp only [hty]; exact e4 a z
            hol := ?_
            der := fun ℓ => by rw [hl']; exact Wt.der ℓ.1 ℓ.2
            fr := Y.fr
            fr_hol := fun j => by simp only [hl]; exact Y.c2 j
            fr_ne := fun j z => by rw [hl]; exact Y.c3 j z
            fr_g := fun j j' z => by rw [hl]; exact Y.c4 j j' z
            fr_0 := fun j => by rw [hl]; exact Y.c5 j
            χ := fun v => Y.χl (pv (U.X k) idx x.1 v)
            χ_norm := ?_
            fr_per := ?_ }, ?_⟩, hhx⟩
  · rw [hl']
    intro V f
    have := ReciprocityTheory.ChartRestriction.G.TB.ValAt.famHol Wt.F (Wt.ik k) Wt.Pm Wt.per V f
    simpa only [Set.mem_univ, true_and] using this
  · intro v hv
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [← hpv]
    obtain ⟨j, -⟩ := TopologicalSpace.Opens.mem_iSup.1
      (Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((ex 0).left (IsLocalRing.closedPoint ℂ))))
    exact (Y.c6 a j 0).1
  · intro v hv j z
    obtain ⟨a, rfl⟩ := hsurj v hv
    rw [hl, ← hpv, ← hhx, ← hhx]
    exact (Y.c6 a j z).2
  · intro j z pt
    show _ = (ex z).left → _ → ⊤ ≤ (ex z).left ⁻¹ᵁ _ → _ = Y.θ z * Y.fr j z ^ (1 : ℤ)
    rw [hl, zpow_one]
    exact Y.c7 j z pt

end Fibre

variable {D : D7}

theorem rat_eq_of_archM {W : HSp D} {τ : D.host.E →+* ℂ} {t : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (ht : IsInfEmb τ t) {γ γ' h : GA D W} (hγ : γ ∈ GQ W) (hγ' : γ' ∈ GQ W)
    (e : archM W t (γ * h) = archM W t (γ' * h)) : γ = γ' := by
  have hmul : ∀ g g' : GA D W, archM W t (g * g') = archM W t g * archM W t g' := fun g g' => by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  have h : archM W t γ = archM W t γ' := by
    rw [← mul_inv_cancel_right γ h, ← mul_inv_cancel_right γ' h, hmul (γ * h), hmul (γ' * h), e]
  have key : ∀ δ : GA D W, ∀ δ₀ : GL (Fin W.rank) D.host.E,
      (∀ i j, (matHom W δ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j) → ∀ i j, archM W t δ i j = τ (δ₀.1 i j) := by
    intro δ δ₀ he i j
    change t (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom W δ).1 i j)) = _
    rw [he, Algebra.TensorProduct.map_tmul, map_one]
    exact ht.1 _
  obtain ⟨δ₀, -, he⟩ := hγ
  obtain ⟨δ₁, -, he'⟩ := hγ'
  have h0 : ∀ i j, (matHom W γ).1 i j = (1 : AF D.host.F) ⊗ₜ δ₀.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he).symm
  have h1 : ∀ i j, (matHom W γ').1 i j = (1 : AF D.host.F) ⊗ₜ δ₁.1 i j := fun i j =>
    (congrArg (fun x : GL (Fin W.rank) (AF D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) he').symm
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  refine (h0 i j).trans (Eq.trans ?_ (h1 i j).symm)
  rw [τ.injective ((key γ δ₀ h0 i j).symm.trans ((congrFun (congrFun h i) j).trans (key γ' δ₁ h1 i j)))]

theorem atComp_of_frAt {W : HSp D} {S : D.what₂.Tau → Finset (ℚ × Bool)} (M : Formalism.IndefR.Mult.DSModel W S) {θ : InfFam D}
    (hθ : IsInfFam θ) {r : ℕ} (hr : W.rank = r) {Comp : Type} {X : Comp → Data D.host.E r}
    {dict : GA D W → Σ k, Frame (X k).Ψ r} {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} (h0 : IsModelBaseFrameFamily M hr x₀)
    (hΨ : ∀ k, ∀ τ ∈ (X k).Ψ, ∃ ρ, τ = tauE D ρ) {h γ γ₀ : GA D W} (hγ : γ ∈ GQ W) (hf : FrAt M θ hr dict γ h)
    (hx : (dict h).2 ∈ (X (dict h).1).dom) (ha : AtComp θ W hr X dict x₀ h γ₀) : AtComp θ W hr X dict x₀ h γ := by
  obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ (X (dict h).1).Ψ := by
    obtain ⟨τ₀⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    by_cases h' : ComplexEmbedding.conjugate τ₀ ∈ (X (dict h).1).Ψ
    · exact ⟨_, h'⟩
    · exact ⟨τ₀, ((X (dict h).1).cmType τ₀).2 h'⟩
  obtain ⟨ρ, rfl⟩ := hΨ _ τ hτ
  have hm := hf ρ ⟨_, hτ⟩ rfl
  rw [← h0.mul] at hm
  have hm' : mat (dict h).2 ⟨_, hτ⟩ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM W (θ ρ) (γ₀ * h)) * x₀ (tauE D ρ) := by
    rw [← CcModel.realM_mt hθ W (γ₀ * h) (tauE D ρ) ⟨ρ, rfl⟩ _ (hθ ρ)]
    exact congrFun ha.2.2 ⟨_, hτ⟩
  have hd : (mat (dict h).2 ⟨_, hτ⟩).det ≠ 0 := (hx ⟨_, hτ⟩).1
  rw [hm, Matrix.det_mul] at hd
  have hu : IsUnit (x₀ (tauE D ρ)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (right_ne_zero_of_mul hd))
  obtain rfl : γ = γ₀ := rat_eq_of_archM (hθ ρ) hγ ha.1 ((Matrix.reindex _ _).injective
    (hu.mul_right_cancel (hm.symm.trans hm')))
  exact ha

theorem realPt_fin (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X).map (finPart D) = 0 := by
  ext i j
  change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 1 0 ⊗ₜ X i j) = 0
  rw [Algebra.TensorProduct.map_tmul]
  exact TensorProduct.zero_tmul _ _

theorem realM_realPt {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    {τ : D.host.E →+* ℂ} (hτ : ∃ ρ, τ = tauE D ρ) (i j) :
    realM θ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T X) τ i j = τ (X i j) := by
  rw [realM, dite_eq_left hτ]
  change θ hτ.choose (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    (pairA D.host.F 1 0 ⊗ₜ X i j)) = _
  rw [Algebra.TensorProduct.map_tmul]
  have := (hθ hτ.choose).1 (X i j)
  rw [← hτ.choose_spec] at this
  exact this

theorem isONLatBasis_one {i : Fin D.R.m} (h : VStd D i) : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) 1 := by
  refine ⟨fun a a' => ?_, ?_⟩
  · rw [h.1]
    simp [Matrix.one_apply, apply_ite, eq_comm]
  · rw [← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, h.2, SetLike.coe_set_eq]
    apply le_antisymm
    · intro x hx
      choose y hy using fun a => Submodule.mem_one.1 (hx a trivial)
      rw [show x = ∑ a, y a • fun i' => (1 : Matrix _ _ D.host.E) i' a from funext fun b => by
        simp [Matrix.one_apply, ← hy, Algebra.smul_def]]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩ b -
      show (1 : Matrix _ _ D.host.E) b a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
      rw [Matrix.one_apply]
      split_ifs
      · exact Submodule.mem_one.2 ⟨1, map_one _⟩
      · exact zero_mem _

theorem exists_atComp_cast (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (W : HSp D) (hV : T.V j σ = W) (hr : W.rank = D.R.r) {θ : InfFam D} (hθ : IsInfFam θ)
    (hΨ : ∀ k, ∀ τ ∈ ((T.U j σ).X k).Ψ, ∃ ρ, τ = tauE D ρ) (h : GA D W) :
    ∃ γ, AtComp θ W hr (T.U j σ).X (castDict hV (T.dict j σ)) (T.x₀ j σ) h γ := by
  subst hV
  obtain ⟨_, g, e, F, ik, φ, th, -, -, h3, h4⟩ := hL.adPin j hj σ hσ
  exact CcModel.exists_atComp hθ hr (T.U j σ) (T.dict j σ) _ e F ik φ th _ hΨ h3 h4 h


set_option maxHeartbeats 1000000 in
theorem framePin_of_ccIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i), σ = T.σ₀ → LawsJ T → R.models_inf → VStd D i → IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) σ) → GlobalTheory.AdTh.CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) (T.U ((i : ℕ) + 1) σ) (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.x₀ ((i : ℕ) + 1) σ) (R.ωP i A.μ0) (R.vacP i) (T.cE ((i : ℕ) + 1) σ) → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV := by
  intro D G _ _ Pl0 T0 A T _ R i σ hV hσ hL hθ hS h0 hcc
  have hj := inR i
  have hg : GoodEmb T.Q.c σ := hσ ▸ T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hΨ : ∀ k, ∀ τ ∈ ((T.U ((i : ℕ) + 1) σ).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hL.pins.1 τ (((hU.2.1 k).2 τ).1 hτ)
  refine ⟨1, 1, norm_one, isONLatBasis_one hS, fun h γ hγ hf hx Wt Y X z hz => ?_⟩
  obtain ⟨γ₀, ha⟩ := exists_atComp_cast T hL _ hj σ hg _ hV (rank_Wc i) hθ hΨ h
  have ha' := atComp_of_frAt _ hθ (rank_Wc i) h0 hΨ hγ hf hx ha
  obtain ⟨bas, idx, hb, hi, hgr, hH⟩ := exists_genReads_of_unitAt hg hU hr1 Wt Y
  have key := hcc.2 h γ ha' hx Wt.g bas idx Wt.e hb hi Y.θ hgr _ (realPt_fin (Vc D i) (Wc D i) X)
  have hzz : AdTh.zOf R.θ (Vc D i) (Wc D i) (rank_Wc i) _ idx (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2
      (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) = z := by
    funext a j
    rw [hz a, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec, ← hi.1, pv, Function.comp_apply, ← perC_emb, AdTh.zOf]
    congr 1
    funext τ m
    rw [realM_realPt hθ _ _ _ (hΨ _ _ τ.2)]
    simp [Matrix.one_apply, Data.emb]
  rw [hzz] at key
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt_eq, key]
  simp only [hH]
  rw [neg_mul, Complex.exp_neg]
  have := Complex.exp_ne_zero ((Real.pi / 2 : ℂ) * ∑ a, GlobalTheory.Dict.hx _ bas idx (castDict hV (T.dict ((i : ℕ) + 1) σ) h).2 (z a) (z a))
  field_simp

end GlobalTheory.FrameConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

section Family

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

def IsCan {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X}
    (pm : Gx x₁ ⟶ Gx x) : Prop :=
  x₁ = spMap χ ≫ x ∧ pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₁) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left ≫ spMap χ

def IsFib {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X}
    (Ψ : Gx x ⟶ Gx x') (Ψ₁ : Gx x₁ ⟶ Gx x₁') : Prop :=
  ∃ (pm : Gx x₁ ⟶ Gx x) (pm' : Gx x₁' ⟶ Gx x'), IsCan χ pm ∧ IsCan χ pm' ∧ Ψ₁ ≫ pm' = pm ≫ Ψ ∧
    Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left

def IsHeckeFam (P : Ideal (𝓞 E)) (p i : ℕ) {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} (Ψ : Gx x ⟶ Gx x') : Prop :=
  IsLinHom Ψ ∧ Etale Ψ ∧ Surjective Ψ ∧ (∃ β, IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2) β) ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
      IsFib χ Ψ Ψ₁ → Xo.univ.t.HeckeKer (Over.mk x₁) Dw P p i (transKer Xo.univ.t.G Ψ₁) ∧
        IsHeckeIsog p (transKer Xo.univ.t.G Ψ₁) Ψ₁

def IsListed {T : Type} [CommRing T] {x x' : Sp T ⟶ Xo.X} (Ψ : Gx x ⟶ Gx x') {n : ℕ}
    (σ : Fin n → (Over.mk x ⟶ Xo.univ.t.G)) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'),
    IsFib χ Ψ Ψ₁ → ∃ e : Fin n ≃ transKer Xo.univ.t.G Ψ₁, ∀ j, (e j).1.left = spMap χ ≫ (σ j).left

theorem exists_isCan {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X}
    (hx : x₁ = spMap χ ≫ x) : ∃ pm : Gx x₁ ⟶ Gx x, IsCan χ pm :=
  ⟨pullback.lift (pullback.fst (Over.mk x₁).hom Xo.univ.t.G.hom ≫ spMap χ)
      (pullback.snd (Over.mk x₁).hom Xo.univ.t.G.hom)
      (by
        show pullback.fst (Over.mk x₁).hom Xo.univ.t.G.hom ≫ spMap χ ≫ x =
          pullback.snd (Over.mk x₁).hom Xo.univ.t.G.hom ≫ Xo.univ.t.G.hom
        rw [← hx]
        exact pullback.condition), hx, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem exists_isFib {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X}
    {x₁ x₁' : Sp Ω ⟶ Xo.X} (hx : x₁ = spMap χ ≫ x) (hx' : x₁' = spMap χ ≫ x') (Ψ : Gx x ⟶ Gx x')
    (hΨ : Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left) :
    ∃ Ψ₁ : Gx x₁ ⟶ Gx x₁', IsFib χ Ψ Ψ₁ := by
  obtain ⟨pm, hp⟩ := exists_isCan χ hx
  obtain ⟨pm', hp'⟩ := exists_isCan χ hx'
  let Ψ₁ : Gx x₁ ⟶ Gx x₁' := pullback.lift (f := (Over.mk x₁').hom) (g := Xo.univ.t.G.hom)
    (fst (Over.mk x₁) Xo.univ.t.G).left (pm ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left) (by
      simp only [Category.assoc]
      rw [GlobalTheory.HeckeFrCompare.snd_hom, reassoc_of% hΨ, reassoc_of% hp.2.2, ← hx']
      rfl)
  have a : Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left := pullback.lift_fst _ _ _
  have b : Ψ₁ ≫ (snd (Over.mk x₁') Xo.univ.t.G).left = pm ≫ Ψ ≫ (snd (Over.mk x') Xo.univ.t.G).left :=
    pullback.lift_snd _ _ _
  refine ⟨Ψ₁, pm, pm', hp, hp', GlobalTheory.HeckeFrCompare.gx_ext ?_ ?_, a⟩
  · rw [Category.assoc, Category.assoc, hp'.2.2, hΨ, hp.2.2, reassoc_of% a]
  · rw [Category.assoc, Category.assoc, hp'.2.1, b]

@[reducible] def fieldCAt {K : Type} [Field K] (σ : K →+* ℂ) : Field (CAt σ) :=
  { (inferInstance : CommRing (CAt σ)), (inferInstanceAs (Field ℂ) : Field (CAt σ)) with }

theorem algClosedCAt {K : Type} [Field K] (σ : K →+* ℂ) : @IsAlgClosed (CAt σ) (fieldCAt σ) :=
  inferInstanceAs (IsAlgClosed ℂ)

def HkPtC {c : Coeff l} {σ : c.F →+* ℂ} (p : ℕ) (y : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G))
    (z : FrPt Xo c (CAt σ)) : Prop :=
  @HkPt E _ _ _ H Dw l Xo c p (CAt σ) (fieldCAt σ) (algClosedCAt σ) _
    (@hkTr E _ _ _ H Dw l Xo c p (CAt σ) (fieldCAt σ) (algClosedCAt σ) _) y C z

end Family

section Match

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Dict GlobalTheory.LevelCusp
open scoped Matrix ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

structure QMatch (X X' : Data E r) (N : ℕ) (a : GL (Fin r) E) : Prop where
  psi : X.Ψ = X'.Ψ
  p0 : X.p0 = X'.p0
  xi : X.ξ0 = X'.ξ0
  iso : ∀ u v, herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u) ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm X.Gm u v
  lat : ∀ v ∈ X.Λ, (N : E) • ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) ∈ X'.Λ
  lat' : ∀ w ∈ X'.Λ, (N : E) • (((a⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) ∈ X.Λ

variable {X X' : Data E r} {N : ℕ} {a : GL (Fin r) E}

theorem QMatch.mem (h : QMatch X X' N a) (τ : X'.Ψ) : τ.1 ∈ X.Ψ := by rw [h.psi]; exact τ.2

theorem QMatch.hermC_eq (h : QMatch X X' N a) (τ : E →+* ℂ) (u v : Fin r → ℂ) :
    hermC τ X'.Gm ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ u) ((a : Matrix (Fin r) (Fin r) E).map τ *ᵥ v) =
      hermC τ X.Gm u v := by
  rw [hermC_of_herm (ε := 1) (fun u v => by rw [h.iso, one_mul]), map_one, one_mul]

theorem QMatch.dmin_eq (h : QMatch X X' N a) (x : Frame X.Ψ r) (τ : X'.Ψ) (i : Fin (r + 1)) :
    dmin X'.Gm (lact a (castFr h.psi x)) τ i = dmin X.Gm x ⟨τ.1, h.mem τ⟩ i := by
  unfold dmin
  congr 1
  ext p q
  exact h.hermC_eq τ.1 (col (mat x ⟨τ.1, h.mem τ⟩) p) (col (mat x ⟨τ.1, h.mem τ⟩) q)

theorem QMatch.mem_dom (h : QMatch X X' N a) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    lact a (castFr h.psi x) ∈ X'.dom := fun τ => by
  refine ⟨?_, fun i => by rw [h.dmin_eq, ← h.p0]; exact (hx _).2 i⟩
  have e : mat (lact a (castFr h.psi x)) τ =
      (a : Matrix (Fin r) (Fin r) E).map τ.1 * mat x ⟨τ.1, h.mem τ⟩ := rfl
  rw [e, Matrix.det_mul]
  refine mul_ne_zero ?_ (hx _).1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, map_ne_zero]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 a.isUnit).ne_zero

end Match

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLeftInverseLiftingSplitPlaceInverses
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.MatrixLeftInverseLift

theorem matrix_left_inverse_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ} (v : Pl (F := F)) (π₁ π₂ : AE F E →+* Fv F v), (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ K : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) (K - 1) →
  ∀ N₁ N₂ : Matrix (Fin d) (Fin d) (Fv F v), N₁ * K.map π₁ = 1 → N₂ * K.map π₂ = 1 →
  ∃ M : Matrix (Fin d) (Fin d) (AE F E), M * K = 1 ∧ M.map π₁ = N₁ ∧ M.map π₂ = N₂ := by
  intro F E _ _ _ _ _ d v π₁ π₂ hinj hsurj K hK N₁ N₂ h₁ h₂
  choose Z hZA hZ₁ hZ₂ using fun i j => hsurj ((N₁ - 1) i j) ((N₂ - 1) i j)
  let Zm : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of Z
  have hZm : ∀ u, evFin F v u = 0 → u • Zm = 0 := by
    intro u hu; ext i j; simpa [Zm] using hZA i j u hu
  have hmap : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (∀ i j, π (Z i j) = (N - 1) i j) → (Zm + 1).map π = N := by
    intro π N hπ
    ext i j
    have h := hπ i j
    by_cases hij : i = j
    · subst hij; simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, h]
    · simp [Zm, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply, hij, h]
  have hM₁ := hmap π₁ N₁ hZ₁
  have hM₂ := hmap π₂ N₂ hZ₂
  refine ⟨Zm + 1, ?_, hM₁, hM₂⟩
  have hdecomp : (Zm + 1) * K - 1 = Zm * (K - 1) + Zm + (K - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_mul, one_mul]; abel
  have hAt : ∀ u, evFin F v u = 0 → u • ((Zm + 1) * K - 1) = 0 := by
    intro u hu
    rw [hdecomp, smul_add, smul_add, ← Matrix.mul_smul, hK u hu, hZm u hu]; simp
  have hπ : ∀ (π : AE F E →+* Fv F v) (N : Matrix (Fin d) (Fin d) (Fv F v)),
      (Zm + 1).map π = N → N * K.map π = 1 → ((Zm + 1) * K - 1).map π = 0 := by
    intro π N hM hN
    have : π.mapMatrix ((Zm + 1) * K - 1) = π.mapMatrix (Zm + 1) * π.mapMatrix K - 1 := by
      rw [map_sub, map_mul, map_one]
    change π.mapMatrix ((Zm + 1) * K - 1) = 0
    rw [this]; change (Zm + 1).map π * K.map π - 1 = 0
    rw [hM, hN, sub_self]
  have e₁ := hπ π₁ N₁ hM₁ h₁
  have e₂ := hπ π₂ N₂ hM₂ h₂
  rw [← sub_eq_zero]
  ext i j
  apply hinj
  · intro u hu
    have := congrArg (fun m => m i j) (hAt u hu)
    simpa using this
  · simpa using congrArg (fun m => m i j) e₁
  · simpa using congrArg (fun m => m i j) e₂

end GlobalTheory.MatrixLeftInverseLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTranslateFlagUnipotentHeightLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.FlagHeight

theorem exists_rat_translate_height_le : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C := by
  intro D S S₀ ρ d
  obtain ⟨KU, hKU, hU⟩ := GlobalTheory.UnitU.cocompact D ρ
  obtain ⟨KR, hKR, hR⟩ := GlobalTheory.Unf.FlagSub.radX_cocompact d
  have hlv : Continuous (GlobalTheory.JacMeas.lv d) := d.continuous_levi.comp continuous_subtype_val
  have hc : Continuous fun q : radX d × UX D ρ => q.1.1 * GlobalTheory.JacMeas.lv d q.2 :=
    (continuous_subtype_val.comp continuous_fst).mul (hlv.comp continuous_snd)
  have hK : IsCompact ((fun q : radX d × UX D ρ => q.1.1 * GlobalTheory.JacMeas.lv d q.2) '' (KR ×ˢ KU)) :=
    (hKR.prod hKU).image hc
  obtain ⟨C, hC⟩ := exists_height_le_of_isCompact S hK
  refine ⟨C, fun n hn => ?_⟩
  obtain ⟨n₀, hn₀, u, rfl⟩ := GlobalTheory.JacMeas.exists_rad_lv d hn
  obtain ⟨γu, hγu, k, hk, rfl⟩ := hU u
  have hr : (GlobalTheory.JacMeas.lv d γu)⁻¹ * n₀ * ((GlobalTheory.JacMeas.lv d γu)⁻¹)⁻¹ ∈ radX d := by
    have := GlobalTheory.JacMeas.lv_conj d n₀ hn₀ γu⁻¹
    simpa [map_inv] using this
  obtain ⟨γr, hγr, kr, hkr, hrk⟩ := hR ⟨_, hr⟩
  have hlvQ : GlobalTheory.JacMeas.lv d γu ∈ GQ S := d.levi_mem_GQ hγu.1 hγu.2
  have hγrQ : (γr : GA D S) ∈ GQ S := Subgroup.mem_subgroupOf.1 hγr
  refine ⟨(γr : GA D S)⁻¹ * (GlobalTheory.JacMeas.lv d γu)⁻¹, mul_mem (inv_mem hγrQ) (inv_mem hlvQ),
    mul_mem (inv_mem (GlobalTheory.JacMeas.radX_le d γr.2)) (inv_mem (GlobalTheory.JacMeas.lv_mem d γu)), ?_⟩
  apply hC
  refine ⟨(kr, k), ⟨hkr, hk⟩, ?_⟩
  have e : ((γr : GA D S) * kr) = (GlobalTheory.JacMeas.lv d γu)⁻¹ * n₀ * ((GlobalTheory.JacMeas.lv d γu)⁻¹)⁻¹ := by
    have := congrArg Subtype.val hrk
    simpa using this.symm
  simp only
  rw [map_mul]
  calc (kr : GA D S) * GlobalTheory.JacMeas.lv d k
      = (γr : GA D S)⁻¹ * ((γr : GA D S) * kr) * GlobalTheory.JacMeas.lv d k := by group
    _ = _ := by rw [e]; group

end GlobalTheory.FlagHeight
end

