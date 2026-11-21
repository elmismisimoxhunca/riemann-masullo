module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
public import RiemannMasullo.AppC_LCTVS.Sec2b
public import RiemannMasullo.AppA_AlgebraicNT.Sec1
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.MetricSpace.Ultra.Basic
import RiemannMasullo.ForMathlib.Algebra.Module.ZLattice.Quotient
import RiemannMasullo.ForMathlib.Topology.Algebra.Group.Divisible
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.LocalSubgroup
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Complex.CircleLocalHom
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Compact
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Order.WellQuasiOrder
import Mathlib.Topology.Homotopy.Lifting

/-!
# Structure of locally compact abelian groups and their Schwartz–Bruhat spaces

Masullo, §§D.1.4–D.1.5, pp. 757–765.
-/

@[expose] public noncomputable section

open Bornology Filter MeasureTheory Set Topology TopologicalSpace
open scoped Cardinal ContDiff DirectSum Topology

namespace RiemannMasullo

section Structure

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.4.1, p. 757. A compact neighborhood of the identity
generates the whole group. -/
def IsCompactlyGeneratedGroup (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U : Set G, U ∈ 𝓝 (1 : G) ∧ IsCompact U ∧ Subgroup.closure U = ⊤

/-- Paper: Definition D.1.4.1, p. 757. A compact group is compactly generated.
Deviation: Sanity check using the whole group as the generating neighborhood. -/
theorem isCompactlyGeneratedGroup_of_compact [CompactSpace G] :
    IsCompactlyGeneratedGroup G :=
  ⟨Set.univ, Filter.univ_mem, isCompact_univ, Subgroup.closure_univ⟩

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean space admits charts in
some fixed finite real dimension. -/
def IsLocallyEuclidean (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ n : ℕ, Nonempty (ChartedSpace (EuclideanSpace ℝ (Fin n)) X)

/-- Paper: Theorem D.1.4.2, p. 757. A discrete space is locally Euclidean in
dimension zero.
Deviation: Sanity check for the locally Euclidean condition. -/
theorem isLocallyEuclidean_of_discrete (X : Type*) [TopologicalSpace X]
    [DiscreteTopology X] : IsLocallyEuclidean X :=
  ⟨0, ⟨ChartedSpace.ofDiscreteTopology⟩⟩

/-- Paper: (D.1.4.2), p. 757. A presentation identifies a group topologically
with a product of real, torus, free discrete and finite factors.
Deviation: The finite factor is enumerated by `Fin finiteOrder`. -/
structure ElementaryLCAPresentation (G : Type*) [CommGroup G] [TopologicalSpace G] where
  realDim : ℕ
  torusDim : ℕ
  latticeRank : ℕ
  finiteOrder : ℕ
  finiteGroup : AddCommGroup (Fin finiteOrder)
  equiv : letI := finiteGroup
    G ≃ₜ* Multiplicative (ElementaryLieGroup realDim torusDim latticeRank (Fin finiteOrder))

/-- Paper: (D.1.4.2), p. 757. Two elementary presentations have the same real
dimension, torus dimension and free lattice rank, and isomorphic finite factors.
Deviation: The finite factors are compared up to group isomorphism. -/
theorem ElementaryLCAPresentation.invariants (e e' : ElementaryLCAPresentation G) :
    e.realDim = e'.realDim ∧ e.torusDim = e'.torusDim ∧ e.latticeRank = e'.latticeRank ∧
      Nonempty (@AddEquiv (Fin e.finiteOrder) (Fin e'.finiteOrder)
        e.finiteGroup.toAdd e'.finiteGroup.toAdd) := by sorry

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.4.2, p. 757. A connected, locally Euclidean abelian
topological group admits an additive homomorphism from a finite-dimensional real vector
group that is a local homeomorphism.
Deviation: This isolates the local exponential map. After equipping the group with a
compatible Lie group structure, its exponential is a homomorphism by commutativity
and is a local homeomorphism by the inverse function theorem and translation. -/
theorem exists_euclidean_localHomeomorph {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [T2Space A] [LocallyCompactSpace A] [ConnectedSpace A]
    (hA : IsLocallyEuclidean A) :
    ∃ (k : ℕ) (f : EuclideanSpace ℝ (Fin k) →+ A), IsLocalHomeomorph f := by
  sorry

/-- Paper: Theorem D.1.4.2, p. 757. A locally Euclidean LCA group is a product
of real and torus factors and a discrete abelian group. -/
theorem lca_equiv_real_torus_discrete (hG : IsLocallyEuclidean G) :
    ∃ (m n : ℕ) (D : Type u) (_ : AddCommGroup D) (_ : TopologicalSpace D)
      (_ : DiscreteTopology D),
      Nonempty (G ≃ₜ* Multiplicative (EuclideanSpace ℝ (Fin m) ×
        (Fin n → AddCircle (1 : ℝ)) × D)) := by
  let A := Additive G
  have : T2Space A := ‹T2Space G›
  have : LocallyCompactSpace A := ‹LocallyCompactSpace G›
  let H := AddSubgroup.connectedComponentOfZero A
  obtain ⟨k, ⟨charts⟩⟩ := hG
  let : ChartedSpace (EuclideanSpace ℝ (Fin k)) A := charts
  have : LocallyConnectedSpace A := ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin k)) A
  have hH : IsOpen (H : Set A) := isOpen_connectedComponent
  have : ConnectedSpace H := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have : LocallyCompactSpace H := hH.isOpenEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, f, hf⟩ := exists_euclidean_localHomeomorph (A := H)
    ⟨k, ⟨TopologicalSpace.Opens.instChartedSpace (⟨H, hH⟩ : TopologicalSpace.Opens A)⟩⟩
  have hRange : IsOpen (f.range : Set H) := by
    rw [AddMonoidHom.coe_range, ← Set.image_univ]
    exact hf.isOpenMap _ isOpen_univ
  let U : OpenAddSubgroup H := ⟨f.range, hRange⟩
  have hSurj : Function.Surjective f := by
    have hTop := U.isClopen.eq_univ ⟨0, U.zero_mem⟩
    exact Set.range_eq_univ.mp (by
      change (f.range : Set H) = Set.univ at hTop
      simpa only [AddMonoidHom.coe_range] using hTop)
  have hF : IsOpenQuotientMap f := ⟨hSurj, hf.continuous, hf.isOpenMap⟩
  have hKer : DiscreteTopology f.ker := by
    obtain ⟨V, hV, h0, hinj⟩ := hf.isLocallyInjective 0
    rw [discreteTopology_iff_isOpen_singleton_zero]
    have hs : (Subtype.val : f.ker → EuclideanSpace ℝ (Fin d)) ⁻¹' V = {0} := by
      ext x
      exact ⟨fun hx ↦ Set.mem_singleton_iff.mpr
        (Subtype.ext (hinj hx h0 (x.property.trans (map_zero f).symm))),
        fun hx ↦ by
          obtain rfl := Set.mem_singleton_iff.mp hx
          exact h0⟩
    exact hs ▸ hV.preimage continuous_subtype_val
  let : DivisibleBy H ℤ := divisibleByOfSMulRightSurj H ℤ (fun {z} hz y ↦ by
    obtain ⟨x, rfl⟩ := hSurj y
    have hzR : (z : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hz
    refine ⟨f ((z : ℝ)⁻¹ • x), ?_⟩
    change z • f ((z : ℝ)⁻¹ • x) = f x
    rw [← map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, mul_inv_cancel₀ hzR, one_smul])
  have : DiscreteTopology f.ker.toIntSubmodule := hKer
  -- Both quotient maps have the same kernel, so they induce a topological isomorphism.
  obtain ⟨m, n, q, hQ, hQker⟩ := exists_euclidean_torus_quotient f.ker.toIntSubmodule
  have hSameKer : f.ker = q.ker := hQker.symm
  let eF := QuotientAddGroup.quotientKerEquivOfSurjective f hF.surjective
  let eQ := QuotientAddGroup.quotientKerEquivOfSurjective q hQ.surjective
  let eKer := QuotientAddGroup.quotientAddEquivOfEq hSameKer
  let e := eF.symm.trans (eKer.trans eQ)
  have he (x : EuclideanSpace ℝ (Fin d)) : e (f x) = q x := by
    have hfmk : eF (QuotientAddGroup.mk x) = f x := rfl
    rw [← hfmk]
    change eQ (eKer (eF.symm (eF _))) = _
    rw [eF.symm_apply_apply]
    rfl
  have eH : H ≃ₜ+ EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) :=
    { e with
      continuous_toFun := hF.continuous_comp_iff.mp
        (show Continuous (e ∘ f) from (funext he : e ∘ f = q) ▸ hQ.continuous)
      continuous_invFun := hQ.continuous_comp_iff.mp
        (show Continuous (e.symm ∘ q) from
          (funext fun x ↦ e.symm_apply_eq.mpr (he x).symm : e.symm ∘ q = f) ▸ hF.continuous) }
  obtain ⟨split⟩ := exists_continuousAddEquiv_prod_quotient_of_open H hH
  let D := A ⧸ H
  have : DiscreteTopology D := QuotientAddGroup.discreteTopology hH
  let product := split.toAddEquiv.trans (AddEquiv.prodCongr eH.toAddEquiv (AddEquiv.refl D))
  let assoc := Homeomorph.prodAssoc (EuclideanSpace ℝ (Fin m)) (Fin n → AddCircle (1 : ℝ)) D
  refine ⟨m, n, D, inferInstance, inferInstance, inferInstance, ⟨{
    AddEquiv.toMultiplicativeRight (product.trans AddEquiv.prodAssoc) with
    continuous_toFun := assoc.continuous.comp
      ((eH.continuous_toFun.prodMap continuous_id).comp split.continuous_toFun)
    continuous_invFun := split.continuous_invFun.comp
      ((eH.continuous_invFun.prodMap continuous_id).comp assoc.symm.continuous) }⟩⟩

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- The compact-open neighborhoods of the trivial character test values on compact sets. -/
private theorem pontryaginDual_nhds_one_hasBasis :
    (𝓝 (1 : PontryaginDual G)).HasBasis
      (fun p : Set G × Set Circle ↦ IsCompact p.1 ∧ p.2 ∈ 𝓝 (1 : Circle))
      (fun p ↦ {χ | MapsTo χ p.1 p.2}) := by
  let f : PontryaginDual G → C(G, Circle) := ContinuousMonoidHom.toContinuousMap
  have hf : IsInducing f := ContinuousMonoidHom.isInducing_toContinuousMap G Circle
  rw [hf.nhds_eq_comap]
  exact ((𝓝 (1 : Circle)).basis_sets.nhds_continuousMapConst (X := G)).comap f

/-- Paper: Theorem D.1.4.3(1), p. 757. A locally compact Hausdorff abelian group
with a continuous homomorphism to a finite-dimensional torus and discrete kernel
is locally Euclidean.
Deviation: This isolates the local chart construction. On a sufficiently small
compact identity neighborhood the homomorphism is an embedding. In logarithm
coordinates its image near zero is a relatively closed local additive subgroup
of a finite-dimensional real vector space, hence locally a linear subspace.
Translation gives charts at every point. -/
theorem isLocallyEuclidean_of_discrete_torus_kernel {ι : Type*} [Finite ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  sorry

open scoped Pointwise in
/-- A neighborhood containing no nontrivial cyclic subgroup lets finitely many
characters detect the identity locally. -/
private theorem isLocallyEuclidean_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) : IsLocallyEuclidean G := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pontryaginDual_pairing_separates (G := G)).1
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine isLocallyEuclidean_of_discrete_torus_kernel f
    (discreteTopology_of_isOpen_singleton_one ?_)
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

open scoped Pointwise in
/-- Circle-valued characters lift to real logarithms on a simply connected chart.
These logarithms rule out nontrivial cyclic subgroups in a smaller neighborhood. -/
private theorem exists_nhds_one_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    ∃ W ∈ 𝓝 (1 : G), ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
  obtain ⟨n, ⟨charts⟩⟩ := hG
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E (1 : G)
  have he : (1 : G) ∈ e.source := mem_chart_source E 1
  obtain ⟨r, hr, hrb⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source he))
  -- Pull back a ball to obtain a simply connected identity neighborhood.
  let B := Metric.ball (e 1) r
  let U := e.symm '' B
  have hU : IsOpen U := (e.symm.isOpen_image_iff_of_subset_source hrb).mpr Metric.isOpen_ball
  have h1U : (1 : G) ∈ U :=
    ⟨e 1, Metric.mem_ball_self hr, e.left_inv he⟩
  let b : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hrb rfl
  let : ContractibleSpace B := (convex_ball _ _).contractibleSpace ⟨_, Metric.mem_ball_self hr⟩
  let : SimplyConnectedSpace U := b.symm.toHomotopyEquiv.simplyConnectedSpace
  let : LocallyPathConnectedSpace B := Metric.isOpen_ball.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace U := b.locallyPathConnectedSpace
  let : LocallyConnectedSpace G := ChartedSpace.locallyConnectedSpace E G
  obtain ⟨V₀, hV₀, h1V₀, hprod⟩ := exists_open_nhds_one_mul_subset (hU.mem_nhds h1U)
  obtain ⟨V, ⟨hV, h1V, hVconn⟩, hVsub⟩ :=
    (LocallyConnectedSpace.open_connected_basis (1 : G)).mem_iff.mp (hV₀.mem_nhds h1V₀)
  have hVV : V * V ⊆ U := (Set.mul_subset_mul hVsub hVsub).trans hprod
  have hVU : V ⊆ U := fun x hx ↦ hVV (mul_one x ▸ Set.mul_mem_mul hx h1V)
  obtain ⟨K, hK, hKV, hKc⟩ := local_compact_nhds (hV.mem_nhds h1V)
  refine ⟨K, hK, fun x hx ↦ ?_⟩
  apply (pontryaginDual_pairing_separates (G := G)).1
  funext χ
  let χU : C(U, Circle) := ⟨fun u ↦ χ u, χ.continuous.comp continuous_subtype_val⟩
  let oneU : U := ⟨1, h1U⟩
  let oneV : V := ⟨1, h1V⟩
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    χU oneU 0 (Circle.exp_zero.trans (map_one χ).symm)
  have hl (u : U) : Circle.exp (L u) = χ u := congrFun hL u
  let incl (v : V) : U := ⟨v, hVU v.property⟩
  let mul (p : V × V) : U := ⟨p.1 * p.2, hVV (Set.mul_mem_mul p.1.property p.2.property)⟩
  let : ConnectedSpace V := isConnected_iff_connectedSpace.mp hVconn
  -- Uniqueness of lifts makes the logarithm additive on pairs from the smaller neighborhood.
  have hAdd (a b : V) : L (mul (a, b)) = L (incl a) + L (incl b) := by
    have hMul : Continuous mul :=
      (continuous_subtype_val.comp continuous_fst).mul
        (continuous_subtype_val.comp continuous_snd) |>.subtype_mk _
    have hIncl : Continuous incl := continuous_subtype_val.subtype_mk _
    have hAgree : Circle.exp ∘ (fun p : V × V ↦ L (mul p)) =
        Circle.exp ∘ (fun p : V × V ↦ L (incl p.1) + L (incl p.2)) := by
      funext p
      simp [Circle.exp_add, hl, mul, incl, map_mul]
    have hStart : L (mul (oneV, oneV)) = L (incl oneV) + L (incl oneV) := by
      have hmul : mul (oneV, oneV) = oneU := Subtype.ext (one_mul 1)
      have hincl : incl oneV = oneU := rfl
      simp [hmul, hincl, hL0]
    exact congrFun (Circle.isCoveringMap_exp.eq_of_comp_eq (L.continuous.comp hMul)
      ((L.continuous.comp (hIncl.comp continuous_fst)).add
        (L.continuous.comp (hIncl.comp continuous_snd))) hAgree (oneV, oneV) hStart) (a, b)
  -- A nonzero logarithm would grow without bound along the powers inside the compact set.
  let z (k : ℕ) : V := ⟨x ^ k, hKV (hx k)⟩
  have hPow (k : ℕ) : L (incl (z k)) = k * L (incl (z 1)) := by
    induction k with
    | zero =>
      have hz : incl (z 0) = oneU := Subtype.ext (pow_zero x)
      simpa [hz] using hL0
    | succ k ih =>
      have hz : incl (z (k + 1)) = mul (z k, z 1) := Subtype.ext (by simp [incl, mul, z, pow_succ])
      rw [hz, hAdd, ih, Nat.cast_succ, add_mul, one_mul]
  have hKb : IsCompact (Subtype.val ⁻¹' K : Set U) := by
    exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hKc
      (Subtype.range_coe.symm ▸ hKV.trans hVU)
  obtain ⟨M, hM⟩ := (hKb.image L.continuous).isBounded.exists_norm_le
  have hZero : L (incl (z 1)) = 0 := by
    by_contra hNe
    obtain ⟨k, hk⟩ := exists_nat_gt (M / ‖L (incl (z 1))‖)
    have hLe := hM _ (mem_image_of_mem L (show incl (z k) ∈ Subtype.val ⁻¹' K from hx k))
    rw [hPow, norm_mul, Real.norm_natCast] at hLe
    exact (not_lt_of_ge hLe) ((div_lt_iff₀ (norm_pos_iff.mpr hNe)).mp hk)
  have hValue := hl (incl (z 1))
  rw [hZero, Circle.exp_zero] at hValue
  simpa [incl, z] using hValue.symm

omit [T2Space G] in
/-- If the dual is locally Euclidean, the subgroup generated by a suitable compact
neighborhood has no nontrivial characters on its quotient, so it equals the whole group. -/
private theorem isCompactlyGeneratedGroup_of_dual_locallyEuclidean
    (h : IsLocallyEuclidean (PontryaginDual G)) : IsCompactlyGeneratedGroup G := by
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean h
  obtain ⟨⟨K, U⟩, ⟨hK, hU⟩, hSub⟩ := pontryaginDual_nhds_one_hasBasis.mem_iff.mp hW
  obtain ⟨L, hL, hLnhds⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (K ∪ L)
  refine ⟨K ∪ L, mem_of_superset hLnhds subset_union_right, hK.union hL, ?_⟩
  have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
    (mem_of_superset hLnhds (subset_union_right.trans Subgroup.subset_closure))
  let : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
  let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
  have hKill (ψ : PontryaginDual (G ⧸ H)) : PontryaginDual.map q ψ = 1 := by
    let φ : G →ₜ* Circle := PontryaginDual.map q ψ
    apply hPow
    intro k
    apply hSub
    intro x hx
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr
      (Subgroup.subset_closure (Or.inl hx))
    change (φ ^ k) x ∈ U
    rw [ContinuousMonoidHom.pow_apply]
    change (PontryaginDual.map q ψ x) ^ k ∈ U
    rw [PontryaginDual.map_apply, hqx, map_one, one_pow]
    exact mem_of_mem_nhds hU
  refine eq_top_iff.mpr fun x _ ↦ (QuotientGroup.eq_one_iff x).mp ?_
  apply (pontryaginDual_pairing_separates (G := G ⧸ H)).1
  funext ψ
  exact DFunLike.congr_fun (hKill ψ) x |>.trans (map_one ψ).symm

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. An LCA group is compactly generated
exactly when its dual is locally Euclidean. -/
theorem isCompactlyGeneratedGroup_iff_dual_locallyEuclidean :
    IsCompactlyGeneratedGroup G ↔ IsLocallyEuclidean (PontryaginDual G) := by
  constructor
  · rintro ⟨K, _, hK, hGen⟩
    have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
      simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
    refine isLocallyEuclidean_of_noSmallCyclicSubgroups
      (pontryaginDual_nhds_one_hasBasis.mem_of_mem (i := (K, _)) ⟨hK, hC⟩) ?_
    intro χ hχ
    have hTrivial : K ⊆ (χ : G →ₜ* Circle).toMonoidHom.ker := by
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      let φ : G →ₜ* Circle := χ
      change φ x ^ k ∈ Circle.centeredArc (Real.pi / 2)
      rw [← ContinuousMonoidHom.pow_apply]
      exact hχ k hx
    have hTop : ⊤ ≤ (χ : G →ₜ* Circle).toMonoidHom.ker :=
      hGen ▸ (Subgroup.closure_le _).mpr hTrivial
    exact PontryaginDual.ext fun x ↦ MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top x))
  · exact isCompactlyGeneratedGroup_of_dual_locallyEuclidean

open scoped Pointwise in
-- Retain the Hausdorff and local compactness assumptions in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.4.3(1), p. 757. A closed subgroup of a compactly generated
LCA group is compactly generated. -/
theorem isCompactlyGeneratedGroup_closedSubgroup (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup H := by
  classical
  obtain ⟨U, hU, hUc, hGen⟩ := hG
  -- Write every element as a product of finitely many fixed directions and a remainder in U.
  obtain ⟨t, ht⟩ := compact_covered_by_mul_left_translates
    ((hUc.union hUc.inv).mul hUc) ⟨1, mem_interior_iff_mem_nhds.mpr hU⟩
  let a (n : t → ℕ) : G := ∏ i : t, ((i : G)⁻¹) ^ n i
  have ha0 : a 0 = 1 := by simp [a]
  have haAdd (m n : t → ℕ) : a (m + n) = a m * a n := by
    simp only [a, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  have haSingle (i : t) : a (Pi.single i 1) = (i : G)⁻¹ := by
    unfold a
    rw [Finset.prod_eq_single i (fun j _ hj ↦ by rw [Pi.single_eq_of_ne hj, pow_zero])
      (fun hi ↦ (hi (Finset.mem_univ i)).elim), Pi.single_eq_same, pow_one]
  have hStep (x : G) (hx : x ∈ U ∪ U⁻¹) (y : G)
      (hy : ∃ n : t → ℕ, ∃ u ∈ U, y = a n * u) :
      ∃ n : t → ℕ, ∃ u ∈ U, x * y = a n * u := by
    obtain ⟨n, u, hu, rfl⟩ := hy
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (ht (Set.mul_mem_mul hx hu))
    change i * (x * u) ∈ U at hiu
    refine ⟨n + Pi.single ⟨i, hi⟩ 1, i * (x * u), hiu, ?_⟩
    rw [haAdd, haSingle]
    simp [mul_assoc, mul_left_comm]
  have hRepresent (x : G) : ∃ n : t → ℕ, ∃ u ∈ U, x = a n * u := by
    have hx : x ∈ Subgroup.closure U := hGen.symm ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction_left (p := fun z _ ↦ ∃ n : t → ℕ, ∃ u ∈ U, z = a n * u)
      ⟨0, 1, mem_of_mem_nhds hU, by simp [ha0]⟩ ?_ ?_ hx
    · exact fun z hz y _ ↦ hStep z (Or.inl hz) y
    · exact fun z hz y _ ↦ hStep z⁻¹ (Or.inr (by simpa using hz)) y
  obtain ⟨V, hV, _, hVinv, hVV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hU
  obtain ⟨s, hs⟩ := compact_covered_by_mul_left_translates hUc
    ⟨1, mem_interior_iff_mem_nhds.mpr hV⟩
  -- For each translate, Dickson's lemma bounds the minimal nonzero exponent vectors.
  let P (i : s) (n : t → ℕ) : Prop :=
    n ≠ 0 ∧ ∃ u ∈ U, (i : G) * u ∈ V ∧ a n * u ∈ H
  let M : Set (t → ℕ) := {0} ∪ ⋃ i : s, {n | Minimal (P i) n}
  have hM : M.Finite := (finite_singleton 0).union (finite_iUnion fun i ↦
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (P i)))
  let K : Set G := (a '' M) * U
  let S : Set H := Subtype.val ⁻¹' K
  let J : Subgroup G := (Subgroup.closure S).map H.subtype
  have hK : IsCompact K := (hM.image a).isCompact.mul hUc
  have hUK : U ⊆ K := by
    intro u hu
    rw [← one_mul u, ← ha0]
    exact Set.mul_mem_mul (mem_image_of_mem a (Or.inl rfl)) hu
  have hMem (x : G) (hx : x ∈ H) (hxK : x ∈ K) : x ∈ J :=
    Subgroup.mem_map.mpr ⟨⟨x, hx⟩, Subgroup.subset_closure hxK, rfl⟩
  have hReduce (n : t → ℕ) : ∀ u ∈ U, a n * u ∈ H → a n * u ∈ J := by
    refine wellFounded_lt.induction (C := fun m ↦ ∀ u ∈ U, a m * u ∈ H → a m * u ∈ J) n ?_
    clear n
    intro n ih u hu hnu
    by_cases hn : n = 0
    · exact hMem _ hnu (Set.mul_mem_mul (mem_image_of_mem a (Or.inl hn)) hu)
    obtain ⟨i, hi, hiu⟩ := mem_iUnion₂.mp (hs hu)
    let j : s := ⟨i, hi⟩
    obtain ⟨m, hmn, hm⟩ := exists_minimal_le_of_wellFoundedLT (P j) n
      ⟨hn, u, hu, hiu, hnu⟩
    obtain ⟨hm0, v, hv, hiv, hmv⟩ := hm.prop
    obtain ⟨d, hd⟩ := exists_add_of_le hmn
    have hdn : d < n := by
      rw [hd]
      exact lt_add_of_pos_left d (lt_of_le_of_ne (fun i ↦ Nat.zero_le (m i)) hm0.symm)
    have huv : u / v ∈ U := by
      have hInv : (i * v)⁻¹ ∈ V := hVinv ▸ Set.mem_inv.mpr (by simpa using hiv)
      have hMul := hVV (Set.mul_mem_mul hiu hInv)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hMul
    have hFactor : a n * u = (a m * v) * (a d * (u / v)) := by
      rw [hd, haAdd]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    have hdH : a d * (u / v) ∈ H := by
      simpa only [hFactor, inv_mul_cancel_left] using H.mul_mem (H.inv_mem hmv) hnu
    rw [hFactor]
    exact J.mul_mem (hMem _ hmv (Set.mul_mem_mul (mem_image_of_mem a
      (Or.inr (mem_iUnion.mpr ⟨j, hm⟩))) hv)) (ih d hdn (u / v) huv hdH)
  refine ⟨S, continuous_subtype_val.continuousAt.preimage_mem_nhds (mem_of_superset hU hUK),
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK, eq_top_iff.mpr ?_⟩
  intro x _
  obtain ⟨n, u, hu, hx⟩ := hRepresent x
  have hxJ : (x : G) ∈ J := hx ▸ hReduce n u hu (hx ▸ x.property)
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxJ
  exact (Subtype.ext hyx : y = x) ▸ hy

-- Retain the LCA and closedness assumptions in the existing signature.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: Theorem D.1.4.3(1), p. 757. The quotient of a compactly generated LCA
group by a closed subgroup is compactly generated. -/
theorem isCompactlyGeneratedGroup_quotient (hG : IsCompactlyGeneratedGroup G)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) : IsCompactlyGeneratedGroup (G ⧸ H) := by
  obtain ⟨U, hU, hCompact, hGen⟩ := hG
  let q := QuotientGroup.mk' H
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨q '' U, ?_, hCompact.image hq.continuous, ?_⟩
  · simpa only [map_one] using hq.isOpenMap.image_mem_nhds hU
  · rw [← MonoidHom.map_closure, hGen, Subgroup.map_top_of_surjective q hq.surjective]

/-- Paper: Theorem D.1.4.3(2), p. 757. An LCA group has an elementary presentation
exactly when it is compactly generated and locally Euclidean. -/
theorem lca_elementary_iff :
    (IsCompactlyGeneratedGroup G ∧ IsLocallyEuclidean G) ↔
      Nonempty (ElementaryLCAPresentation G) := by sorry

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: (D.1.4.3), p. 758. The indexing set consists of open compactly
generated subgroups ordered by inclusion. -/
abbrev OpenCompactlyGeneratedSubgroups (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {H : Subgroup G // IsOpen (H : Set G) ∧ IsCompactlyGeneratedGroup H}

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: (D.1.4.3), p. 758. The open compactly generated subgroups are filtered
and cover the group. The topology is final for their open inclusions. -/
theorem openCompactlyGeneratedSubgroups_colimit :
    IsDirectedOrder (OpenCompactlyGeneratedSubgroups G) ∧
      (∀ x : G, ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val) ∧
      (∀ U : Set G, IsOpen U ↔
        ∀ H : OpenCompactlyGeneratedSubgroups G, IsOpen (Subtype.val ⁻¹' U : Set H.val)) := by
  let ofCompactNeighborhood (K : Set G) (hK : IsCompact K) (hKnhds : K ∈ 𝓝 (1 : G)) :
      OpenCompactlyGeneratedSubgroups G := by
    let H := Subgroup.closure K
    have hH : IsOpen (H : Set G) := H.isOpen_of_mem_nhds
      (mem_of_superset hKnhds Subgroup.subset_closure)
    exact ⟨H, hH, Subtype.val ⁻¹' K,
      continuous_subtype_val.continuousAt.preimage_mem_nhds hKnhds,
      (H.isClosed_of_isOpen hH).isClosedEmbedding_subtypeVal.isCompact_preimage hK,
      Subgroup.closure_preimage_eq_top K⟩
  have hCover (x : G) : ∃ H : OpenCompactlyGeneratedSubgroups G, x ∈ H.val := by
    obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
    exact ⟨ofCompactNeighborhood (insert x K) (hK.insert x)
      (mem_of_superset hKnhds (subset_insert x K)), Subgroup.subset_closure (mem_insert x K)⟩
  refine ⟨⟨?_⟩, hCover, ?_⟩
  · intro H J
    obtain ⟨A, hAnhds, hA, hAgen⟩ := H.property.2
    obtain ⟨B, _, hB, hBgen⟩ := J.property.2
    have hAnhds' : H.val.subtype '' A ∈ 𝓝 (1 : G) :=
      H.property.1.isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hAnhds
    let L := ofCompactNeighborhood (H.val.subtype '' A ∪ J.val.subtype '' B)
      ((hA.image continuous_subtype_val).union (hB.image continuous_subtype_val))
      (mem_of_superset hAnhds' subset_union_left)
    have hL : L.val = H.val ⊔ J.val := by
      change Subgroup.closure (H.val.subtype '' A ∪ J.val.subtype '' B) = _
      rw [Subgroup.closure_union, ← MonoidHom.map_closure, ← MonoidHom.map_closure,
        hAgen, hBgen, Subgroup.map_top, Subgroup.map_top, Subgroup.range_subtype,
        Subgroup.range_subtype]
    exact ⟨L, le_sup_left.trans hL.ge, le_sup_right.trans hL.ge⟩
  · intro U
    refine ⟨fun hU H ↦ hU.preimage continuous_subtype_val, ?_⟩
    intro hU
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    obtain ⟨H, hxH⟩ := hCover x
    have hImage := H.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ (hU H)
    exact mem_of_superset (hImage.mem_nhds ⟨⟨x, hxH⟩, hx, rfl⟩)
      (fun _ ⟨_, hy, hEq⟩ ↦ hEq ▸ hy)

omit [T2Space G] in
/-- Every compact set is contained in an open compactly generated subgroup. -/
private theorem exists_openCompactlyGeneratedSubgroup_contains {K : Set G} (hK : IsCompact K) :
    ∃ H : OpenCompactlyGeneratedSubgroups G, K ⊆ (H.val : Set G) := by
  obtain ⟨U, hU, hU₁⟩ := exists_compact_mem_nhds (1 : G)
  let H := Subgroup.closure (U ∪ K)
  have hSubset : U ∪ K ⊆ (H : Set G) := Subgroup.subset_closure
  have hOpen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_of_superset hU₁ (subset_union_left.trans hSubset))
  refine ⟨⟨H, hOpen, ⟨Subtype.val ⁻¹' (U ∪ K), ?_, ?_, ?_⟩⟩,
    subset_union_right.trans hSubset⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_of_superset hU₁ subset_union_left)
  · exact IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hU.union hK)
      (Subtype.range_coe.symm ▸ hSubset)
  · exact Subgroup.closure_preimage_eq_top _

/-- Paper: Lemma D.1.4.4, p. 758. Evaluation on the open compactly generated
subgroups of the dual identifies the group with their duals' inverse limit.
Deviation: The limit is expressed as the range in the product, with the subspace topology. -/
theorem lca_dualSubgroups_inverseLimit :
    let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
    ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val),
      (∀ x H (χ : H.val), γ x H χ = χ.val x) ∧ IsEmbedding γ ∧
        range γ = {a | ∀ (H J : I) (h : H ≤ J) (χ : H.val),
          a H χ = a J (Subgroup.inclusion h χ)} := by
  classical
  let I := OpenCompactlyGeneratedSubgroups (PontryaginDual G)
  change ∃ γ : G →ₜ* ((H : I) → PontryaginDual H.val), _
  have hCover (χ : PontryaginDual G) : ∃ H : I, χ ∈ H.val := by
    obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains (isCompact_singleton (x := χ))
    exact ⟨H, hH (mem_singleton χ)⟩
  have hDirected (H J : I) : ∃ L : I, H ≤ L ∧ J ≤ L := by
    obtain ⟨U, _, hU, hUgen⟩ := H.property.2
    obtain ⟨V, _, hV, hVgen⟩ := J.property.2
    obtain ⟨L, hL⟩ := exists_openCompactlyGeneratedSubgroup_contains
      ((hU.image continuous_subtype_val).union (hV.image continuous_subtype_val))
    have hLe (M : I) {S : Set M.val} (hGen : Subgroup.closure S = ⊤)
        (hSub : Subtype.val '' S ⊆ (L.val : Set (PontryaginDual G))) : M ≤ L := by
      have hTop : (⊤ : Subgroup M.val) ≤ L.val.comap M.val.subtype :=
        hGen ▸ (Subgroup.closure_le _).mpr (fun x hx ↦ hSub (mem_image_of_mem Subtype.val hx))
      exact fun x hx ↦ hTop (Subgroup.mem_top (⟨x, hx⟩ : M.val))
    exact ⟨L, hLe H hUgen (subset_union_left.trans hL), hLe J hVgen (subset_union_right.trans hL)⟩
  let restrict (H : I) : PontryaginDual (PontryaginDual G) →ₜ* PontryaginDual H.val :=
    PontryaginDual.map ⟨H.val.subtype, continuous_subtype_val⟩
  let γ : G →ₜ* ((H : I) → PontryaginDual H.val) :=
    { toFun := fun x H ↦ restrict H (pontryaginDual_eval x)
      map_one' := funext fun H ↦ (restrict H).comp pontryaginDual_eval |>.map_one
      map_mul' := fun x y ↦ funext fun H ↦ (restrict H).comp pontryaginDual_eval |>.map_mul x y
      continuous_toFun := continuous_pi fun H ↦ (restrict H).continuous.comp
        (pontryaginDual_eval (G := G)).continuous }
  have hEval (x : G) (H : I) (χ : H.val) : γ x H χ = χ.val x := rfl
  refine ⟨γ, hEval, ⟨?_, ?_⟩, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto γ (𝓝 1) (𝓝 (γ 1)) := γ.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      -- A single coordinate contains all the characters needed to test this neighborhood.
      obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
      obtain ⟨H, hH⟩ := exists_openCompactlyGeneratedSubgroup_contains hK
      have hKH : IsCompact (Subtype.val ⁻¹' K : Set H.val) :=
        IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK (Subtype.range_coe.symm ▸ hH)
      let V : Set (PontryaginDual H.val) :=
        {ψ | MapsTo ψ (Subtype.val ⁻¹' K) (Metric.ball 1 (1 / 4))}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo hKH Metric.isOpen_ball).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap H.val Circle).continuous
      refine Filter.mem_comap.mpr ⟨(fun a ↦ a H) ⁻¹' V,
        (hV.preimage (continuous_apply H)).mem_nhds ?_, ?_⟩
      · intro χ _
        simp [Metric.mem_ball]
      · intro x hx
        apply hTest x
        intro χ hχ
        exact hx (show (⟨χ, hH hχ⟩ : H.val) ∈ Subtype.val ⁻¹' K from hχ)
  · intro x y hxy
    apply (pontryaginDual_pairing_separates (G := G)).1
    funext χ
    obtain ⟨H, hH⟩ := hCover χ
    exact congrArg (fun a ↦ a H ⟨χ, hH⟩) hxy
  · ext a
    constructor
    · rintro ⟨x, rfl⟩ H J h χ
      rfl
    · intro ha
      change ∀ (H J : I) (h : H ≤ J) (χ : H.val),
        a H χ = a J (Subgroup.inclusion h χ) at ha
      choose H hH using hCover
      let f (χ : PontryaginDual G) := a (H χ) ⟨χ, hH χ⟩
      -- Compatibility makes the chosen subgroup irrelevant.
      have hf (J : I) (χ : J.val) : f χ.val = a J χ := by
        obtain ⟨L, h₁, h₂⟩ := hDirected (H χ.val) J
        exact (ha _ _ h₁ _).trans (ha _ _ h₂ χ).symm
      let J := H 1
      let ψ : PontryaginDual (PontryaginDual G) :=
        { toFun := f
          map_one' := (hf J 1).trans (map_one (a J))
          map_mul' := fun χ ξ ↦ by
            obtain ⟨L, hχ, hξ⟩ := hDirected (H χ) (H ξ)
            let χL : L.val := ⟨χ, hχ (hH χ)⟩
            let ξL : L.val := ⟨ξ, hξ (hH ξ)⟩
            exact (hf L (χL * ξL)).trans
              ((map_mul (a L) χL ξL).trans (congrArg₂ (· * ·) (hf L χL).symm (hf L ξL).symm))
          continuous_toFun := by
            rw [continuous_iff_continuousAt]
            intro χ
            let J := H χ
            have hComp : f ∘ (Subtype.val : J.val → PontryaginDual G) = a J := funext (hf J)
            exact J.property.1.isOpenEmbedding_subtypeVal.continuousAt_iff.mp
              (hComp.symm ▸ (a J).continuous.continuousAt (x := (⟨χ, hH χ⟩ : J.val))) }
      obtain ⟨e, he⟩ := pontryaginDual_bidual (G := G)
      refine ⟨e.symm ψ, funext fun J ↦ PontryaginDual.ext fun χ ↦ ?_⟩
      rw [hEval, ← he, e.apply_symm_apply]
      exact hf J χ

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator consists of characters
whose restriction to the subgroup is trivial. -/
def lcaAnnihilator (H : Subgroup G) : Subgroup (PontryaginDual G) :=
  (PontryaginDual.map (⟨H.subtype, continuous_subtype_val⟩ : H →ₜ* G)).toMonoidHom.ker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Paper: Definition D.1.4.5, p. 758. The annihilator in the original group is
the intersection of the kernels of the characters in the given subgroup. -/
def lcaDualAnnihilator (J : Subgroup (PontryaginDual G)) : Subgroup G :=
  ⨅ χ : J, (show G →ₜ* Circle from χ.val).toMonoidHom.ker

/-- Paper: Definition D.1.4.5, p. 758. A character is in the annihilator exactly
when its value on every element of the subgroup is one. -/
theorem mem_lcaAnnihilator_iff (H : Subgroup G) (χ : PontryaginDual G) :
    χ ∈ lcaAnnihilator H ↔ ∀ x : H, χ x.val = 1 := by
  rw [lcaAnnihilator, MonoidHom.mem_ker]
  constructor
  · intro h x
    exact congrArg (fun ψ : PontryaginDual H ↦ ψ x) h
  · exact fun h ↦ PontryaginDual.ext h

/-- Paper: Definition D.1.4.5, p. 758. A group element is in the dual annihilator
exactly when every character of the subgroup takes value one there. -/
theorem mem_lcaDualAnnihilator_iff (J : Subgroup (PontryaginDual G)) (x : G) :
    x ∈ lcaDualAnnihilator J ↔ ∀ χ : J, χ.val x = 1 :=
  Subgroup.mem_iInf

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.1.4.6(1), p. 758. Taking the annihilator twice recovers a
closed subgroup under the evaluation pairing. -/
theorem lcaDualAnnihilator_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    lcaDualAnnihilator (lcaAnnihilator H) = H := by
  ext x
  rw [mem_lcaDualAnnihilator_iff]
  constructor
  · intro hx
    let : T1Space (G ⧸ H) := QuotientGroup.t1Space_iff.mpr hH
    let q : G →ₜ* (G ⧸ H) := ⟨QuotientGroup.mk' H, QuotientGroup.continuous_mk⟩
    apply (QuotientGroup.eq_one_iff x).mp
    apply (pontryaginDual_pairing_separates (G := G ⧸ H)).1
    funext ψ
    have hψ : PontryaginDual.map q ψ ∈ lcaAnnihilator H := by
      apply (mem_lcaAnnihilator_iff H _).mpr
      intro y
      have hy : q y.val = 1 := (QuotientGroup.eq_one_iff y.val).mpr y.property
      rw [PontryaginDual.map_apply, hy, map_one]
    exact (hx ⟨PontryaginDual.map q ψ, hψ⟩).trans (map_one ψ).symm
  · intro hx χ
    exact (mem_lcaAnnihilator_iff H χ.val).mp χ.property ⟨x, hx⟩

/-- Paper: Lemma D.1.4.6(2), p. 758. Pullback by the quotient map identifies
the dual of a quotient with the annihilator. -/
theorem lcaQuotientDual_equiv_annihilator (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : PontryaginDual (G ⧸ H) ≃ₜ* lcaAnnihilator H,
      ∀ (χ : PontryaginDual (G ⧸ H)) x, (e χ).val x = χ (QuotientGroup.mk x) := by sorry

/-- Paper: Lemma D.1.4.6(2), p. 758. Restriction of characters identifies the
dual modulo the annihilator with the dual of the subgroup. -/
theorem lcaDualQuotient_equiv_subgroupDual (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ e : (PontryaginDual G ⧸ lcaAnnihilator H) ≃ₜ* PontryaginDual H,
      ∀ (χ : PontryaginDual G) (x : H), e (QuotientGroup.mk χ) x = χ x.val := by sorry

/-- Paper: Lemma D.1.4.6(3), p. 758. The annihilator of a compact subgroup is open. -/
theorem isOpen_lcaAnnihilator (H : Subgroup G) (hH : IsCompact (H : Set G)) :
    IsOpen (lcaAnnihilator H : Set (PontryaginDual G)) := by sorry

/-- Paper: Lemma D.1.4.6(4), p. 758. The annihilator of an open subgroup is compact. -/
theorem isCompact_lcaAnnihilator (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (lcaAnnihilator H : Set (PontryaginDual G)) := by sorry

/-- Paper: (D.1.4.9)–(D.1.4.10), p. 759. The evaluation map onto the dual of
an open compactly generated subgroup of the dual is an open quotient. Its
kernel is the compact annihilator of the subgroup. -/
theorem lca_dualSubgroup_quotient (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G)) :
    ∃ γ : G →ₜ* PontryaginDual H.val,
      (∀ x (χ : H.val), γ x χ = χ.val x) ∧ IsOpenQuotientMap γ ∧
        γ.toMonoidHom.ker = lcaDualAnnihilator H.val ∧ IsCompact (γ.toMonoidHom.ker : Set G) := by sorry

-- TODO(paper-gap): p. 759 calls the quotient codomains Uᵢ small subgroups of G.
-- The kernels Kᵢ are the subgroups that become small, as on p. 760.

/-- Paper: After (D.1.4.10), p. 759. Every identity neighborhood contains
one of the compact annihilators.
Deviation: The small subgroups are the kernels Kᵢ, as stated on p. 760. -/
theorem exists_lcaDualAnnihilator_subset_nhds {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ H : OpenCompactlyGeneratedSubgroups (PontryaginDual G),
      (lcaDualAnnihilator H.val : Set G) ⊆ U := by sorry

-- TODO(paper-gap): The component group of Aᵢⱼ can be infinite, as for G = ℤ with
-- Gⱼ = ℤ and Kᵢ = 1. Its component group is finitely generated by (D.1.4.12).

/-- Paper: (D.1.4.12), p. 759. A quotient in the inverse system of an open
compactly generated subgroup has an elementary presentation. -/
theorem lca_openSubgroup_quotient_elementary (J : OpenCompactlyGeneratedSubgroups G)
    (H : OpenCompactlyGeneratedSubgroups (PontryaginDual G))
    (_h : lcaDualAnnihilator H.val ≤ J.val) :
    Nonempty (ElementaryLCAPresentation (J.val ⧸ (lcaDualAnnihilator H.val).comap J.val.subtype)) := by
  sorry

/-- Paper: Lemma D.1.4.7, p. 760. Each open compactly generated subgroup is the
inverse limit of its quotients by the annihilators it contains.
Deviation: We express the compatible families as the range in the product. At comparable
indices the coordinates are compatible exactly when they have a common representative.
Together with the open exhaustion (D.1.4.3), this realizes (D.1.4.16). -/
theorem lca_openSubgroup_inverseLimit (J : OpenCompactlyGeneratedSubgroups G) :
    let I := {H : OpenCompactlyGeneratedSubgroups (PontryaginDual G) //
      lcaDualAnnihilator H.val ≤ J.val}
    let K : I → Subgroup J.val := fun H ↦ (lcaDualAnnihilator H.val.val).comap J.val.subtype
    let δ : J.val → ((H : I) → J.val ⧸ K H) := fun x _ ↦ QuotientGroup.mk x
    Nonempty I ∧ IsDirectedOrder I ∧
      IsEmbedding δ ∧ range δ = {a | ∀ (H H' : I), H ≤ H' →
      ∃ x : J.val, δ x H = a H ∧ δ x H' = a H'} := by sorry

end Structure

section StructuralPairs

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.1(1), p. 760. A good subgroup is closed and has an
open compactly generated annihilator in the dual. -/
def IsBruhatGoodSubgroup (k : Subgroup G) : Prop :=
  IsClosed (k : Set G) ∧ IsOpen (lcaAnnihilator k : Set (PontryaginDual G)) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)

/-- Paper: Definition D.1.5.1(2), p. 760. A structural pair consists of an open
compactly generated subgroup and a good subgroup contained in it.
The order enlarges the first subgroup and shrinks the second. -/
abbrev BruhatStructuralPair (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  {p : Subgroup G × (Subgroup G)ᵒᵈ //
    IsOpen (p.1 : Set G) ∧ IsCompactlyGeneratedGroup p.1 ∧
      IsBruhatGoodSubgroup (OrderDual.ofDual p.2) ∧ OrderDual.ofDual p.2 ≤ p.1}

/-- Paper: (D.1.5.2), p. 761. The quotient associated to a pair divides the
open subgroup by the good subgroup inside it. -/
abbrev BruhatStructuralPair.quotient (p : BruhatStructuralPair G) :=
  p.val.1 ⧸ (OrderDual.ofDual p.val.2).comap p.val.1.subtype

/-- Paper: (D.1.5.2), p. 761. The quotient sends a point to the identity if and
only if it belongs to the good subgroup. -/
theorem BruhatStructuralPair.quotient_mk_eq_one (p : BruhatStructuralPair G) (x : p.val.1) :
    (QuotientGroup.mk x : p.quotient) = 1 ↔ (x : G) ∈ OrderDual.ofDual p.val.2 := by
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_comap, Subgroup.coe_subtype]

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

omit [T2Space G] in
open scoped Pointwise in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel has a
continuous local section over a ball in a linear subspace of the logarithm space. The
section is a local homomorphism, and the images of small balls are identity neighborhoods. -/
theorem exists_localSection_of_discrete_torusKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    ∃ (L : Submodule ℝ (EuclideanSpace ℝ ι)) (ρ : ℝ) (σ : L → G), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ v : L, ‖v‖ < ρ → ∀ i, f (σ v) i = Circle.exp ((v : EuclideanSpace ℝ ι) i)) ∧
      ContinuousOn σ (Metric.ball 0 ρ) ∧
      (∀ v w : L, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → σ (v + w) = σ v * σ w) ∧
      (∀ ε > 0, σ '' Metric.ball 0 ε ∈ 𝓝 1) := by
  classical
  let ex : EuclideanSpace ℝ ι → (ι → Circle) := fun v i ↦ Circle.exp (v i)
  have hex : Continuous ex := continuous_pi fun i ↦ Circle.exp.continuous.comp (by fun_prop)
  have hex0 : ex 0 = 1 := funext fun i ↦ by simp [ex]
  have hexadd : ∀ v w, ex (v + w) = ex v * ex w := fun v w ↦ funext fun i ↦ by
    simp [ex, Circle.exp_add]
  have hexneg : ∀ v, ex (-v) = (ex v)⁻¹ := fun v ↦ funext fun i ↦ by simp [ex]
  -- A neighborhood meeting the kernel only at the identity.
  obtain ⟨O, hO, h1O, hOker⟩ : ∃ O : Set G, IsOpen O ∧ (1 : G) ∈ O ∧
      ∀ x ∈ O, f x = 1 → x = 1 := by
    have hopen1 : IsOpen ({1} : Set f.toMonoidHom.ker) := isOpen_discrete _
    obtain ⟨U0, hU0o, hpre⟩ := isOpen_induced_iff.mp hopen1
    refine ⟨U0, hU0o, ?_, ?_⟩
    · have : (1 : f.toMonoidHom.ker) ∈ Subtype.val ⁻¹' U0 := by rw [hpre]; rfl
      simpa using this
    · intro x hx hfx
      have hmem : (⟨x, MonoidHom.mem_ker.mpr hfx⟩ : f.toMonoidHom.ker) ∈
          Subtype.val ⁻¹' U0 := hx
      rw [hpre] at hmem
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
  obtain ⟨W, hW, h1W, hWW⟩ := exists_open_nhds_one_mul_subset (hO.mem_nhds h1O)
  have hWW' : W ∩ W⁻¹ ∈ 𝓝 (1 : G) :=
    inter_mem (hW.mem_nhds h1W) (inv_mem_nhds_one G (hW.mem_nhds h1W))
  obtain ⟨V, hV, hVW, hVc⟩ := local_compact_nhds hWW'
  have hinj : ∀ x ∈ V, ∀ y ∈ V, f x = f y → x = y := by
    intro x hx y hy hxy
    have hy' : y⁻¹ ∈ W := (hVW hy).2
    have hm : x * y⁻¹ ∈ O := hWW (Set.mul_mem_mul (hVW hx).1 hy')
    have : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hOker _ hm this)
  obtain ⟨C, hC, -, hCinv, hCC⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV
  have h1C : (1 : G) ∈ C := mem_of_mem_nhds hC
  have hCV : C ⊆ V := fun x hx ↦ by simpa using hCC (Set.mul_mem_mul hx h1C)
  -- Small logarithms of values on `V` come from `C`.
  have hD : IsCompact (f '' (V \ interior C)) :=
    (hVc.diff isOpen_interior).image f.continuous
  have h1D : (1 : ι → Circle) ∉ f '' (V \ interior C) := by
    rintro ⟨x, ⟨hxV, hxC⟩, hfx⟩
    have : x = 1 := hinj x hxV 1 (mem_of_mem_nhds hV) (by rw [hfx, map_one])
    exact hxC (this ▸ mem_interior_iff_mem_nhds.mpr hC)
  obtain ⟨ε, hε, hεD⟩ : ∃ ε > 0, ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε →
      ex v ∉ f '' (V \ interior C) := by
    have hnhds : (f '' (V \ interior C))ᶜ ∈ 𝓝 (ex 0) := by
      rw [hex0]; exact hD.isClosed.isOpen_compl.mem_nhds h1D
    obtain ⟨ε, hε, H⟩ := Metric.mem_nhds_iff.mp (hex.continuousAt hnhds)
    exact ⟨ε, hε, fun v hv ↦ H (by simpa using hv)⟩
  have hlift : ∀ v : EuclideanSpace ℝ ι, ‖v‖ < ε → ∀ x ∈ V, f x = ex v → x ∈ C := by
    intro v hv x hx hfx
    by_contra hxC
    exact hεD v hv ⟨x, ⟨hx, fun h ↦ hxC (interior_subset h)⟩, hfx⟩
  -- The logarithms of the image form a closed local subgroup.
  set R := min (ε / 2) 1 with hRdef
  have hR : 0 < R := lt_min (half_pos hε) one_pos
  have hRε : R < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hR1 : R ≤ 1 := min_le_right _ _
  let A : Set (EuclideanSpace ℝ ι) := {v | ‖v‖ ≤ R ∧ ex v ∈ f '' V}
  have hAc : IsClosed A :=
    (isClosed_le continuous_norm continuous_const).inter
      ((hVc.image f.continuous).isClosed.preimage hex)
  have hA0 : (0 : EuclideanSpace ℝ ι) ∈ A :=
    ⟨by simp [hR.le], ⟨1, mem_of_mem_nhds hV, by rw [map_one, hex0]⟩⟩
  have hAmemC : ∀ v ∈ A, ∃ x ∈ C, f x = ex v := by
    rintro v ⟨hv, x, hx, hfx⟩
    exact ⟨x, hlift v (hv.trans_lt hRε) x hx hfx, hfx⟩
  have hAsym : ∀ v ∈ A, -v ∈ A := by
    intro v hvA
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hvA
    have hxC' : x⁻¹ ∈ C := by rw [← hCinv]; simpa using hxC
    exact ⟨by simpa using hvA.1, x⁻¹, hCV hxC', by rw [map_inv, hfx, hexneg]⟩
  have hAadd : ∀ v ∈ A, ∀ w ∈ A, ‖v + w‖ ≤ R → v + w ∈ A := by
    intro v hv w hw hvw
    obtain ⟨x, hxC, hfx⟩ := hAmemC v hv
    obtain ⟨y, hyC, hfy⟩ := hAmemC w hw
    exact ⟨hvw, x * y, hCC (Set.mul_mem_mul hxC hyC), by rw [map_mul, hfx, hfy, hexadd]⟩
  obtain ⟨L, ε₁, hε₁, hε₁R, hAL⟩ :=
    exists_subspace_ball_eq_of_localSubgroup hR hAc hA0 hAsym hAadd
  have hLA : ∀ v : EuclideanSpace ℝ ι, v ∈ L → ‖v‖ ≤ ε₁ → v ∈ A := by
    intro v hvL hv
    have : v ∈ (L : Set (EuclideanSpace ℝ ι)) ∩ Metric.closedBall 0 ε₁ :=
      ⟨hvL, by simpa using hv⟩
    rw [← hAL] at this
    exact this.1
  have hAL' : ∀ v ∈ A, ‖v‖ ≤ ε₁ → v ∈ L := by
    intro v hvA hv
    have : v ∈ A ∩ Metric.closedBall 0 ε₁ := ⟨hvA, by simpa using hv⟩
    rw [hAL] at this
    exact this.1
  let σ : L → G := fun v ↦ Function.invFunOn f C (ex v)
  have hσ : ∀ v : L, ‖v‖ < ε₁ → σ v ∈ C ∧ f (σ v) = ex v := by
    intro v hv
    exact Function.invFunOn_pos (hAmemC _ (hLA _ v.2 hv.le))
  refine ⟨L, ε₁, σ, hε₁, hε₁R.trans hR1, ?_, ?_, ?_, ?_⟩
  · intro v hv i
    exact congrFun (hσ v hv).2 i
  · rw [continuousOn_iff_continuous_domRestrict]
    let gV : V → (ι → Circle) := fun x ↦ f x
    have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
    have hgV : IsClosedEmbedding gV :=
      (f.continuous.comp continuous_subtype_val).isClosedEmbedding
        (fun x y hxy ↦ Subtype.ext (hinj x x.2 y y.2 hxy))
    let σ' : Metric.ball (0 : L) ε₁ → V := fun v ↦
      ⟨σ v, hCV (hσ v (mem_ball_zero_iff.mp v.2)).1⟩
    have hσ' : Continuous σ' := by
      rw [hgV.isInducing.continuous_iff]
      have e : gV ∘ σ' = fun v : Metric.ball (0 : L) ε₁ ↦ ex ((v : L) : EuclideanSpace ℝ ι) :=
        funext fun v ↦ (hσ v (mem_ball_zero_iff.mp v.2)).2
      rw [e]
      exact hex.comp (continuous_subtype_val.comp continuous_subtype_val)
    exact continuous_subtype_val.comp hσ'
  · intro v w hv hw hvw
    have h1 := hσ v hv
    have h2 := hσ w hw
    have h3 := hσ (v + w) hvw
    refine hinj _ (hCV h3.1) _ (hCC (Set.mul_mem_mul h1.1 h2.1)) ?_
    rw [map_mul, h1.2, h2.2, h3.2, ← hexadd]
    rfl
  · intro ε' hε'
    set ε'' := min ε' ε₁ with hε''def
    have hε'' : 0 < ε'' := lt_min hε' hε₁
    have hnear : ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C ∧
        ∃ u : EuclideanSpace ℝ ι, ‖u‖ < ε'' ∧ ∀ i, Circle.exp (u i) = f x i := by
      refine Filter.Eventually.and (show ∀ᶠ x in 𝓝 (1 : G), x ∈ interior C from
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hC)) ?_
      have ht : Tendsto f (𝓝 (1 : G)) (𝓝 1) := by
        have := (map_continuous f).tendsto (1 : G)
        rwa [map_one] at this
      exact ht.eventually (eventually_exists_small_circleLog hε'')
    apply Filter.mem_of_superset hnear
    rintro x ⟨hxC, u, hu, hux⟩
    have hfx : f x = ex u := funext fun i ↦ (hux i).symm
    have hu1 : ‖u‖ < ε₁ := hu.trans_le (min_le_right _ _)
    have huA : u ∈ A := ⟨hu1.le.trans hε₁R, x, hCV (interior_subset hxC), hfx⟩
    have huL : u ∈ L := hAL' u huA hu1.le
    refine ⟨⟨u, huL⟩, by simpa using hu.trans_le (min_le_left _ _), ?_⟩
    have hs := hσ ⟨u, huL⟩ (by simpa using hu1)
    exact hinj _ (hCV hs.1) _ (hCV (interior_subset hxC)) (by rw [hs.2, hfx])

omit [T2Space G] [LocallyCompactSpace G] in
/-- Translating a chart at the identity gives charts everywhere. -/
theorem isLocallyEuclidean_of_chart_at_one {k : ℕ}
    (e : OpenPartialHomeomorph G (EuclideanSpace ℝ (Fin k))) (he : (1 : G) ∈ e.source) :
    IsLocallyEuclidean G := by
  classical
  exact ⟨k, ⟨{
    atlas := Set.range fun g : G ↦
      ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    chartAt := fun g ↦ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).trans e
    mem_chart_source := fun g ↦ by
      change g ∈ ((Homeomorph.mulLeft g⁻¹).toOpenPartialHomeomorph).source ∩
        (Homeomorph.mulLeft g⁻¹) ⁻¹' e.source
      refine ⟨trivial, ?_⟩
      simpa using he
    chart_mem_atlas := fun g ↦ ⟨g, rfl⟩ }⟩⟩

omit [T2Space G] in
/-- A continuous homomorphism to a finite-dimensional torus with discrete kernel makes
the group locally Euclidean. -/
theorem isLocallyEuclidean_of_torusHom_discreteKernel {ι : Type*} [Fintype ι]
    (f : G →ₜ* (ι → Circle)) (hf : DiscreteTopology f.toMonoidHom.ker) :
    IsLocallyEuclidean G := by
  classical
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hf
  have hσ0 : σ 0 = 1 := by
    have e := hσmul 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    rw [add_zero] at e
    exact mul_eq_left.mp e.symm
  let B := Metric.ball (0 : L) ρ
  let τ : B → G := fun v ↦ σ v
  have hτc : Continuous τ := continuousOn_iff_continuous_domRestrict.mp hσc
  have hτinj : Function.Injective τ := by
    intro v w hvw
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    have hw : ‖(w : L)‖ < ρ := mem_ball_zero_iff.mp w.2
    apply Subtype.ext
    apply Subtype.ext
    refine circleExp_coord_injective (hv.le.trans hρ1) (hw.le.trans hρ1) fun i ↦ ?_
    rw [← hfσ v hv i, ← hfσ w hw i]
    exact congrArg (fun x ↦ f x i) hvw
  have hτopen : IsOpenMap τ := by
    intro S hS
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨v, hvS, rfl⟩
    have hv : ‖(v : L)‖ < ρ := mem_ball_zero_iff.mp v.2
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS v hvS
    set δ' := min δ (ρ - ‖(v : L)‖) with hδ'def
    have hδ' : 0 < δ' := lt_min hδ (sub_pos.mpr hv)
    have hδ'1 : δ' ≤ δ := min_le_left _ _
    have hδ'2 : δ' ≤ ρ - ‖(v : L)‖ := min_le_right _ _
    have hnhds : (fun x ↦ σ v * x) '' (σ '' Metric.ball (0 : L) δ') ∈ 𝓝 (σ v) := by
      rw [← map_mul_left_nhds_one (σ v)]
      exact image_mem_map (hσnhds δ' hδ')
    apply Filter.mem_of_superset hnhds
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    have hw' : ‖w‖ < δ' := mem_ball_zero_iff.mp hw
    have hvw : ‖(v : L) + w‖ < ρ :=
      (norm_add_le _ _).trans_lt (by linarith)
    refine ⟨⟨(v : L) + w, mem_ball_zero_iff.mpr hvw⟩, hδS ?_, ?_⟩
    · rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      simpa using hw'.trans_le hδ'1
    · exact (hσmul v w hv (by linarith [norm_nonneg (v : L)]) hvw)
  have hτ : IsOpenEmbedding τ := .of_continuous_injective_isOpenMap hτc hτinj hτopen
  let iso := (stdOrthonormalBasis ℝ L).repr
  let j : B → EuclideanSpace ℝ (Fin (Module.finrank ℝ L)) := fun v ↦ iso v
  have hj : IsOpenEmbedding j :=
    iso.toHomeomorph.isOpenEmbedding.comp Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  have : Nonempty B := ⟨⟨0, Metric.mem_ball_self hρ⟩⟩
  let e := (hτ.toOpenPartialHomeomorph τ).symm.trans (hj.toOpenPartialHomeomorph j)
  have he : (1 : G) ∈ e.source := by
    simp only [e, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
    exact ⟨⟨0, Metric.mem_ball_self hρ⟩, hσ0⟩
  exact isLocallyEuclidean_of_chart_at_one e he

/-- A neighborhood containing no nontrivial cyclic subgroup gives finitely many characters
whose joint kernel is discrete. -/
theorem exists_torusHom_of_noSmallCyclicSubgroups
    {W : Set G} (hW : W ∈ 𝓝 (1 : G))
    (hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1) :
    ∃ (t : Finset (PontryaginDual G)) (f : G →ₜ* (t → Circle)),
      (∀ x (χ : t), f x χ = χ.val x) ∧ DiscreteTopology f.toMonoidHom.ker := by
  classical
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hV, hOne, hVV⟩ := exists_open_nhds_one_mul_subset (inter_mem hKnhds hW)
  have hVW : V ⊆ W := fun x hx ↦ (hVV (mul_one x ▸ Set.mul_mem_mul hx hOne)).2
  let S (χ : PontryaginDual G) : Set G := {x | χ x ≠ 1}
  have hCover : K \ V ⊆ ⋃ χ, S χ := by
    intro x hx
    have hx1 : x ≠ 1 := fun h ↦ hx.2 (h ▸ hOne)
    have hSep := (pontryaginDual_pairing_separates (G := G)).1
    obtain ⟨χ, hχ⟩ : ∃ χ : PontryaginDual G, χ x ≠ 1 := by
      by_contra! hn
      exact hx1 (hSep (funext fun χ ↦ (hn χ).trans (map_one χ).symm))
    exact mem_iUnion.mpr ⟨χ, hχ⟩
  obtain ⟨t, ht⟩ := (hK.diff hV).elim_finite_subcover S
    (fun χ ↦ (isClosed_eq χ.continuous continuous_const).isOpen_compl) hCover
  let f : G →ₜ* (t → Circle) :=
    { toFun := fun x χ ↦ χ.val x
      map_one' := funext fun χ ↦ map_one χ.val
      map_mul' := fun x y ↦ funext fun χ ↦ map_mul χ.val x y
      continuous_toFun := continuous_pi fun χ ↦ χ.val.continuous }
  refine ⟨t, f, fun _ _ ↦ rfl, discreteTopology_of_isOpen_singleton_one ?_⟩
  have hKer (x : f.toMonoidHom.ker) (hx : (x : G) ∈ V) : x = 1 := by
    have hr (k : ℕ) : (x : G) ^ k ∈ V := by
      induction k with
      | zero => simpa using hOne
      | succ k ih =>
        have hKmem : (x : G) ^ (k + 1) ∈ K :=
          (hVV (pow_succ (x : G) k ▸ Set.mul_mem_mul ih hx)).1
        by_contra hn
        obtain ⟨χ, hχt, hχ⟩ := mem_iUnion₂.mp (ht ⟨hKmem, hn⟩)
        have hχx : χ (x : G) = 1 :=
          congrFun (MonoidHom.mem_ker.mp x.property) ⟨χ, hχt⟩
        exact hχ (by rw [map_pow, hχx, one_pow])
    exact Subtype.ext (hPow x fun k ↦ hVW (hr k))
  have hPreimage : (Subtype.val : f.toMonoidHom.ker → G) ⁻¹' V = {1} := by
    ext x
    exact ⟨fun hx ↦ mem_singleton_iff.mpr (hKer x hx), by
      rintro (rfl : x = 1)
      exact hOne⟩
  exact hPreimage ▸ hV.preimage continuous_subtype_val

/-- The dual of a locally Euclidean LCA group is compactly generated: the characters
from a torus homomorphism with discrete kernel, together with a compact polar
neighborhood, generate it. -/
theorem isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean (hG : IsLocallyEuclidean G) :
    IsCompactlyGeneratedGroup (PontryaginDual G) := by
  classical
  obtain ⟨W, hW, hPow⟩ := exists_nhds_one_of_isLocallyEuclidean hG
  obtain ⟨t, f, hft, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  obtain ⟨L, ρ, σ, hρ, hρ1, hfσ, hσc, hσmul, hσnhds⟩ :=
    exists_localSection_of_discrete_torusKernel f hker
  obtain ⟨r, hr, hpolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  set n : ℕ := Fintype.card t with hn
  set ρ₀ := min (ρ / 4) (r / (n + 1)) with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (by positivity) (by positivity)
  have hρ₀ρ : ρ₀ < ρ / 2 := (min_le_left _ _).trans_lt (by linarith)
  have hnρ₀ : (n : ℝ) * ρ₀ ≤ r := by
    have h1 : ρ₀ ≤ r / (n + 1) := min_le_right _ _
    have h2 : (n : ℝ) * (r / (n + 1)) ≤ r := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    calc (n : ℝ) * ρ₀ ≤ n * (r / (n + 1)) := by gcongr
      _ ≤ r := h2
  set K := σ '' Metric.closedBall (0 : L) ρ₀ with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 ρ₀).image_of_continuousOn
      (hσc.mono (Metric.closedBall_subset_ball (hρ₀ρ.trans (half_lt_self hρ))))
  have hK : K ∈ 𝓝 (1 : G) :=
    mem_of_superset (hσnhds ρ₀ hρ₀) (image_mono Metric.ball_subset_closedBall)
  set P := {χ : PontryaginDual G | MapsTo χ K (Metric.closedBall 1 r)} with hPdef
  have hPc : IsCompact P := hpolar K hK
  have hP : P ∈ 𝓝 (1 : PontryaginDual G) := by
    have h1 := pontryaginDual_nhds_one_hasBasis.mem_of_mem
      (i := (K, Metric.ball (1 : Circle) r)) ⟨hKc, Metric.ball_mem_nhds 1 hr⟩
    exact mem_of_superset h1 fun χ hχ ↦ hχ.mono_right Metric.ball_subset_closedBall
  refine ⟨P ∪ (t : Set (PontryaginDual G)), mem_of_superset hP subset_union_left,
    hPc.union t.finite_toSet.isCompact, ?_⟩
  rw [eq_top_iff]
  intro ψ _
  have hψc : ContinuousAt (fun v : L ↦ ψ (σ v)) 0 :=
    ψ.continuous.continuousAt.comp (hσc.continuousAt (Metric.ball_mem_nhds 0 hρ))
  have hψadd : ∀ v w : L, ‖v‖ < ρ / 2 → ‖w‖ < ρ / 2 →
      ψ (σ (v + w)) = ψ (σ v) * ψ (σ w) := by
    intro v w hv hw
    rw [hσmul v w (by linarith) (by linarith) ((norm_add_le v w).trans_lt (by linarith)),
      map_mul]
  obtain ⟨l, hl⟩ := exists_linearMap_circleExp_of_localHom (half_pos hρ) _ hψc hψadd
  obtain ⟨m, hm⟩ := LinearMap.exists_extend l
  let a : t → ℝ := fun i ↦ m (EuclideanSpace.basisFun t ℝ i)
  let k : t → ℤ := fun i ↦ ⌊a i⌋
  set ψ' := ψ * ∏ i : t, (i.val) ^ (-k i) with hψ'def
  have hψ'P : ψ' ∈ P := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ ρ₀ := mem_closedBall_zero_iff.mp hv
    have hvρ : ‖v‖ < ρ / 2 := hv'.trans_lt hρ₀ρ
    let ev : PontryaginDual G →* Circle :=
      { toFun := fun χ ↦ χ (σ v), map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    have hmv : m (v : EuclideanSpace ℝ t) = ∑ i : t, (v : EuclideanSpace ℝ t) i * a i := by
      conv_lhs => rw [← (EuclideanSpace.basisFun t ℝ).sum_repr (v : EuclideanSpace ℝ t)]
      simp [map_sum, map_smul, a]
    have hlv : l v = m (v : EuclideanSpace ℝ t) := (LinearMap.congr_fun hm v).symm
    have hev : ψ' (σ v) = Circle.exp (∑ i : t, (a i - k i) * (v : EuclideanSpace ℝ t) i) := by
      change ev ψ' = _
      rw [hψ'def, map_mul, map_prod]
      change ψ (σ v) * ∏ i : t, ev (i.val ^ (-k i)) = _
      simp only [map_zpow]
      change ψ (σ v) * ∏ i : t, (i.val (σ v)) ^ (-k i) = _
      have hcoord : ∀ i : t, i.val (σ v) = Circle.exp ((v : EuclideanSpace ℝ t) i) := by
        intro i
        rw [← hft, hfσ v (hvρ.trans (half_lt_self hρ)) i]
      simp only [hcoord, ← Circle.exp_intCast_mul]
      rw [hl v hvρ, hlv, hmv, ← circleExp_sum, ← Circle.exp_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      push_cast
      ring
    rw [hev, Metric.mem_closedBall]
    refine (dist_circleExp_one_le _).trans ?_
    calc |∑ i : t, (a i - k i) * (v : EuclideanSpace ℝ t) i|
        ≤ ∑ i : t, |(a i - k i) * (v : EuclideanSpace ℝ t) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : t, ‖v‖ := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          rw [abs_mul]
          have h0 : 0 ≤ a i - k i := by
            have := Int.fract_nonneg (a i); rwa [Int.fract] at this
          have h1 : a i - k i < 1 := by
            have := Int.fract_lt_one (a i); rwa [Int.fract] at this
          have hvi : |(v : EuclideanSpace ℝ t) i| ≤ ‖v‖ := by
            simpa using PiLp.norm_apply_le (v : EuclideanSpace ℝ t) i
          rw [abs_of_nonneg h0]
          nlinarith [abs_nonneg ((v : EuclideanSpace ℝ t) i)]
      _ = n * ‖v‖ := by simp [hn]
      _ ≤ n * ρ₀ := by gcongr
      _ ≤ r := hnρ₀
  have hψ : ψ = ψ' * ∏ i : t, (i.val) ^ (k i) := by
    rw [hψ'def, mul_assoc, ← Finset.prod_mul_distrib]
    simp
  rw [hψ]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl hψ'P))
    (Subgroup.prod_mem _ fun i _ ↦ Subgroup.zpow_mem _ (Subgroup.subset_closure (Or.inr i.2)) _)

/-- If the dual is compactly generated, the group has a neighborhood of the identity
containing no nontrivial cyclic subgroup, hence it is locally Euclidean. -/
theorem isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
    (h : IsCompactlyGeneratedGroup (PontryaginDual G)) : IsLocallyEuclidean G := by
  obtain ⟨K, -, hK, hGen⟩ := h
  have hC : Circle.centeredArc (Real.pi / 2) ∈ 𝓝 (1 : Circle) := by
    simpa using Circle.hasBasis_centeredArc_div_two_pow.mem_of_mem (i := 0) trivial
  let W : Set G := (pontryaginDual_eval (G := G)) ⁻¹'
    {ψ | MapsTo ψ K (Circle.centeredArc (Real.pi / 2))}
  have hW : W ∈ 𝓝 (1 : G) := by
    have h1 := (pontryaginDual_nhds_one_hasBasis (G := PontryaginDual G)).mem_of_mem
      (i := (K, _)) ⟨hK, hC⟩
    have ht := (map_continuous (pontryaginDual_eval (G := G))).tendsto 1
    rw [map_one] at ht
    exact ht h1
  have hPow : ∀ x : G, (∀ k : ℕ, x ^ k ∈ W) → x = 1 := by
    intro x hx
    let evx : PontryaginDual G →* Circle :=
      { toFun := fun χ ↦ χ x, map_one' := rfl, map_mul' := fun _ _ ↦ rfl }
    have hKx : K ⊆ evx.ker := by
      intro χ hχ
      apply MonoidHom.mem_ker.mpr
      apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
      intro k _
      have := hx k hχ
      change χ (x ^ k) ∈ _ at this
      rwa [map_pow] at this
    have hTop : ⊤ ≤ evx.ker := hGen ▸ (Subgroup.closure_le _).mpr hKx
    apply (pontryaginDual_pairing_separates (G := G)).1
    funext χ
    exact (MonoidHom.mem_ker.mp (hTop (Subgroup.mem_top χ))).trans (map_one χ).symm
  obtain ⟨t, f, -, hker⟩ := exists_torusHom_of_noSmallCyclicSubgroups hW hPow
  exact isLocallyEuclidean_of_torusHom_discreteKernel f hker

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- Compact generation is invariant under topological group isomorphisms. -/
theorem isCompactlyGeneratedGroup_of_continuousMulEquiv {H : Type*} [CommGroup H]
    [TopologicalSpace H] (e : G ≃ₜ* H) (h : IsCompactlyGeneratedGroup G) :
    IsCompactlyGeneratedGroup H := by
  obtain ⟨U, hU, hUc, hGen⟩ := h
  refine ⟨e '' U, ?_, hUc.image e.continuous, ?_⟩
  · have := e.toHomeomorph.isOpenMap.image_mem_nhds hU
    rw [show e.toHomeomorph (1 : G) = 1 from map_one e] at this
    exact this
  · have := MonoidHom.map_closure (e.toMulEquiv.toMonoidHom) U
    rw [hGen, Subgroup.map_top_of_surjective _ e.surjective] at this
    exact this.symm

/-- Paper: Definition D.1.5.1(1), p. 760. The trivial subgroup is good exactly
when the group is locally Euclidean.
Deviation: Sanity check using the fact that its annihilator is the entire dual. -/
theorem isBruhatGoodSubgroup_bot_iff :
    IsBruhatGoodSubgroup (⊥ : Subgroup G) ↔ IsLocallyEuclidean G := by
  have htop : lcaAnnihilator (⊥ : Subgroup G) = ⊤ := by
    ext χ
    simp only [Subgroup.mem_top, iff_true]
    rw [mem_lcaAnnihilator_iff]
    intro x
    rw [Subgroup.mem_bot.mp x.2]
    exact map_one χ
  let eTop : (⊤ : Subgroup (PontryaginDual G)) ≃ₜ* PontryaginDual G :=
    { Subgroup.topEquiv with
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  unfold IsBruhatGoodSubgroup
  rw [htop]
  constructor
  · rintro ⟨-, -, hcg⟩
    exact isLocallyEuclidean_of_isCompactlyGeneratedGroup_dual
      (isCompactlyGeneratedGroup_of_continuousMulEquiv eTop hcg)
  · intro h
    refine ⟨by simp, by simp, ?_⟩
    exact isCompactlyGeneratedGroup_of_continuousMulEquiv eTop.symm
      (isCompactlyGeneratedGroup_dual_of_isLocallyEuclidean h)

/-- Paper: Lemma D.1.5.2, p. 760. Structural pairs form a nonempty directed order. -/
theorem bruhatStructuralPair_filtered :
    Nonempty (BruhatStructuralPair G) ∧ IsDirectedOrder (BruhatStructuralPair G) := by sorry

/-- Paper: Lemma D.1.5.2(1), p. 761. The quotient attached to a structural pair
has an elementary presentation. -/
theorem BruhatStructuralPair.elementary (p : BruhatStructuralPair G) :
    Nonempty (ElementaryLCAPresentation p.quotient) := by sorry

/-- Paper: Lemma D.1.5.2(2), p. 761. The two annihilators form a structural pair
in the dual, with the annihilator of the good subgroup as the open subgroup. -/
theorem BruhatStructuralPair.dual (p : BruhatStructuralPair G) :
    ∃ q : BruhatStructuralPair (PontryaginDual G),
      q.val.1 = lcaAnnihilator (OrderDual.ofDual p.val.2) ∧
      OrderDual.ofDual q.val.2 = lcaAnnihilator p.val.1 := by sorry

section Fourier

variable [MeasurableSpace G] [BorelSpace G]

local instance : MeasurableSpace (PontryaginDual G) := borel _

variable {μ : Measure G} [μ.IsHaarMeasure] [μ.Regular]
variable {ν : Measure (PontryaginDual G)}

-- TODO(paper-gap): D.1.5.2(3) asserts pointwise converses for arbitrary integrable
-- representatives. On ℝ a function nonzero only at 0 has zero Fourier transform.

/-- Paper: Lemma D.1.5.2(3), p. 761. Invariance under a subgroup forces the Fourier
transform to vanish off the annihilator.
Deviation: Stated in the forward direction because pointwise invariance can fail
for an integrable representative of an invariant class. -/
theorem lcaFourier_support_subset_annihilator (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (H : Subgroup G) (_hH : IsClosed (H : Set G)) (hinv : ∀ h : H, ∀ x, f (h.val * x) = f x) :
    Function.support (lcaFourier μ f) ⊆ (lcaAnnihilator H : Set (PontryaginDual G)) := by sorry

/-- Paper: Lemma D.1.5.2(3), p. 761. Support in the open subgroup and invariance
under the good subgroup give the corresponding conditions for the dual pair.
Deviation: Stated in the forward direction because pointwise support and invariance
can fail after changing a representative on a null set. -/
theorem lcaFourier_structuralPair_imp (_hν : IsLCAPlancherelMeasure μ ν)
    {f : G → ℂ} (hf : Integrable f μ) (_hfhat : Integrable (lcaFourier μ f) ν)
    (a : BruhatStructuralPair G) (hs : Function.support f ⊆ (a.val.1 : Set G))
    (hinv : ∀ h : ↥(OrderDual.ofDual a.val.2 : Subgroup G), ∀ x, f (h.val * x) = f x) :
    (∀ χ : lcaAnnihilator a.val.1, ∀ ψ : PontryaginDual G,
      lcaFourier μ f (χ.val * ψ) = lcaFourier μ f ψ) ∧
      Function.support (lcaFourier μ f) ⊆
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)) := by sorry

end Fourier
end StructuralPairs

section SchwartzBruhat

variable {G : Type*} [CommGroup G] [TopologicalSpace G]

/-- Paper: Definition D.1.5.3(1), p. 762. A single good subgroup fixes the
function and its descent to each structural quotient with that subgroup is of class Cᵖ.
The derivatives are tested on the real and torus covers of the discrete fibers. -/
def IsBruhatContDiff (p : ℕ) (f : G → ℂ) : Prop :=
  ∃ k : Subgroup G, IsBruhatGoodSubgroup k ∧ (∀ h : k, ∀ x, f (h.val * x) = f x) ∧
    ∀ a : BruhatStructuralPair G, OrderDual.ofDual a.val.2 = k →
      ∃ f₀ : a.quotient → ℂ, (∀ x : a.val.1, f₀ (QuotientGroup.mk x) = f x.val) ∧
        ∀ (e : ElementaryLCAPresentation a.quotient)
          (z : Fin e.latticeRank → ℤ) (b : Fin e.finiteOrder),
          letI := e.finiteGroup
          ContDiff ℝ (p : ℕ∞) (fun xt ↦ f₀ (e.equiv.symm (Multiplicative.ofAdd
            (elementaryCover xt z b))))

/-- Paper: Definition D.1.5.3(1), p. 762. A function is smooth if it is of class Cᵖ
for every finite order p. -/
def IsBruhatSmooth (f : G → ℂ) : Prop :=
  ∀ p : ℕ, IsBruhatContDiff p f

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, finite
orders of Bruhat differentiability agree with ordinary differentiability.
Deviation: Sanity check on the real group. -/
theorem isBruhatContDiff_real_iff (p : ℕ) (f : Multiplicative ℝ → ℂ) :
    IsBruhatContDiff p f ↔ ContDiff ℝ (p : ℕ∞) (f ∘ Multiplicative.ofAdd) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. On the real additive group, Bruhat
smoothness agrees with ordinary smoothness.
Deviation: Sanity check on the real group. -/
theorem isBruhatSmooth_real_iff (f : Multiplicative ℝ → ℂ) :
    IsBruhatSmooth f ↔ ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) := by sorry

variable [hTop : IsTopologicalGroup G] [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

/-- Paper: Definition D.1.5.3(1), p. 762. The zero function is of class Cᵖ. -/
theorem isBruhatContDiff_zero (p : ℕ) : IsBruhatContDiff p (0 : G → ℂ) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. The sum of two functions of class Cᵖ
is of class Cᵖ. -/
theorem IsBruhatContDiff.add {p : ℕ} {f g : G → ℂ}
    (hf : IsBruhatContDiff p f) (hg : IsBruhatContDiff p g) :
    IsBruhatContDiff p (f + g) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. A complex scalar multiple of a function
of class Cᵖ is of class Cᵖ. -/
theorem IsBruhatContDiff.smul {p : ℕ} {f : G → ℂ}
    (hf : IsBruhatContDiff p f) (z : ℂ) : IsBruhatContDiff p (z • f) := by sorry

/-- Paper: Definition D.1.5.3(1), p. 762. The Cᵖ functions form a complex vector
subspace of the functions on G. -/
def bruhatContDiffSubmodule (p : ℕ) : Submodule ℂ (G → ℂ) where
  carrier := {f | IsBruhatContDiff p f}
  zero_mem' := isBruhatContDiff_zero p
  add_mem' hf hg := hf.add hg
  smul_mem' z _ hf := hf.smul z

/-- Paper: Definition D.1.5.3(1), p. 762. The smooth functions are the
intersection of the Cᵖ subspaces over all finite orders. -/
def bruhatSmoothSubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ p : ℕ, bruhatContDiffSubmodule p

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the Cᵖ submodule is
equivalent to the stated Bruhat differentiability condition. -/
theorem mem_bruhatContDiffSubmodule_iff (p : ℕ) (f : G → ℂ) :
    f ∈ bruhatContDiffSubmodule p ↔ IsBruhatContDiff p f := Iff.rfl

/-- Paper: Definition D.1.5.3(1), p. 762. Membership in the smooth submodule
means Bruhat differentiability at every finite order. -/
theorem mem_bruhatSmoothSubmodule_iff (f : G → ℂ) :
    f ∈ bruhatSmoothSubmodule ↔ IsBruhatSmooth f := by
  simp only [bruhatSmoothSubmodule, Submodule.mem_iInf]
  rfl

omit hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. In an elementary presentation, a stage
is the existing elementary Schwartz space with its seminorm topology. -/
abbrev SchwartzBruhatStage {A : Type*} [CommGroup A] [TopologicalSpace A]
    (e : ElementaryLCAPresentation A) :=
  ElementarySchwartz e.realDim e.torusDim e.latticeRank (Fin e.finiteOrder)

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. A stage function is pulled back along
the quotient and extended by zero outside the open subgroup.
Deviation: The printed composition is reversed and omits restriction to the open subgroup. -/
def schwartzBruhatStageRealization (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : SchwartzBruhatStage e →ₗ[ℂ] (G → ℂ) :=
  letI := e.finiteGroup
  (LinearMap.pi fun x : G ↦
    if hx : x ∈ a.val.1 then
      LinearMap.proj (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
    else 0).comp (elementarySchwartzSubmodule e.realDim e.torusDim e.latticeRank
      (Fin e.finiteOrder)).subtype

open Classical in
/-- Paper: Definition D.1.5.3(2), p. 762. The realization evaluates a stage
function at the quotient coordinate on the open subgroup and vanishes outside it. -/
theorem schwartzBruhatStageRealization_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    letI := e.finiteGroup
    schwartzBruhatStageRealization a e f x =
      if hx : x ∈ a.val.1 then
        f (Multiplicative.toAdd (e.equiv (QuotientGroup.mk ⟨x, hx⟩)))
      else 0 := by
  unfold schwartzBruhatStageRealization
  erw [LinearMap.comp_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

include hTop hT2 hLC in
/-- Paper: Lemma D.1.5.4, p. 762. Pullback to the smaller kernel and extension by
zero to the larger open subgroup give a closed embedding of stages.
Deviation: The map is characterized by equality of the realized functions on G,
which determines the pullback and extension on the elementary quotients. -/
theorem schwartzBruhatStage_transition {a b : BruhatStructuralPair G} (h : a ≤ b)
    (e : ElementaryLCAPresentation a.quotient) (e' : ElementaryLCAPresentation b.quotient) :
    ∃ j : SchwartzBruhatStage e →L[ℂ] SchwartzBruhatStage e',
      (∀ f, schwartzBruhatStageRealization b e' (j f) = schwartzBruhatStageRealization a e f) ∧
        IsClosedEmbedding j := by sorry

/-- Paper: (D.1.5.4), p. 763. The underlying Schwartz–Bruhat submodule is generated
by the realizations in every structural pair and every elementary presentation. -/
def schwartzBruhatSubmodule (G : Type*) [CommGroup G] [TopologicalSpace G] :
    Submodule ℂ (G → ℂ) :=
  ⨆ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
    (schwartzBruhatStageRealization a e).range

/-- Paper: (D.1.5.4), p. 763. The stage realization takes values in the
Schwartz–Bruhat submodule and gives the canonical linear stage map. -/
def schwartzBruhatStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) :
    SchwartzBruhatStage e →ₗ[ℂ] schwartzBruhatSubmodule G :=
  (schwartzBruhatStageRealization a e).codRestrict (schwartzBruhatSubmodule G)
    (fun f ↦ Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem e ⟨f, rfl⟩))

/-- Paper: (D.1.5.4), p. 763. The Schwartz–Bruhat topology is generated by the
seminorms that pull back continuously to each stage.
Deviation: Using all elementary presentations avoids fixing any choice of coordinates. -/
abbrev SchwartzBruhat (G : Type*) [CommGroup G] [TopologicalSpace G] :=
  WithGeneratingSeminorms (schwartzBruhatSubmodule G)
    (Subtype.val : {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
        Continuous (p ∘ schwartzBruhatStageInclusion a e)} → _)

instance : CoeFun (SchwartzBruhat G) (fun _ ↦ G → ℂ) where
  coe f := (show schwartzBruhatSubmodule G from f).val

/-- Paper: (D.1.5.4), p. 763. The stage inclusion evaluates to the function
obtained by pullback and extension by zero. -/
theorem schwartzBruhatStageInclusion_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (f : SchwartzBruhatStage e) (x : G) :
    (show SchwartzBruhat G from schwartzBruhatStageInclusion a e f) x =
      schwartzBruhatStageRealization a e f x := rfl

include hTop hT2 hLC

/-- Paper: Definition D.1.5.3(2), p. 762. A function belongs to the
Schwartz–Bruhat submodule exactly when a single structural pair and a single
elementary Schwartz function realize it. -/
theorem mem_schwartzBruhatSubmodule_iff (f : G → ℂ) :
    f ∈ schwartzBruhatSubmodule G ↔
      ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
        (s : SchwartzBruhatStage e), schwartzBruhatStageRealization a e s = f := by sorry

/-- Paper: (D.1.5.4), p. 763. The topology has the final locally convex property
for the canonical linear stage maps. -/
theorem schwartzBruhat_topology_eq_final :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      locallyConvexFinalTopology
        (fun i : (a : BruhatStructuralPair G) × ElementaryLCAPresentation a.quotient ↦
          (show SchwartzBruhatStage i.2 →ₗ[ℂ] SchwartzBruhat G from
            schwartzBruhatStageInclusion i.1 i.2)) := by sorry

-- TODO(paper-gap): Remark D.1.5.5 identifies global smooth functions with a
-- colimit of the smooth structural quotients. For the same extension-by-zero
-- maps, that colimit contains only functions supported in an open compactly
-- generated subgroup. The constant function 1 on discrete ℚ is smooth but
-- has no such support.

/-- Paper: Remark D.1.5.5, p. 763. Every Schwartz–Bruhat function is smooth in
the sense of Definition D.1.5.3(1). -/
theorem schwartzBruhat_isBruhatSmooth (f : SchwartzBruhat G) : IsBruhatSmooth f := by sorry

/-- Paper: Remark D.1.5.5, p. 763. A character restricts to a smooth function on
each open compactly generated subgroup. -/
theorem pontryaginDual_restriction_isBruhatSmooth (χ : PontryaginDual G)
    (J : OpenCompactlyGeneratedSubgroups G) :
    IsBruhatSmooth (fun x : J.val ↦ (χ x.val : ℂ)) := by sorry

/-- Paper: Lemma D.1.5.6(1), p. 763. The final locally convex topology is Hausdorff
when the group is second countable. -/
theorem schwartzBruhat_t2 [SecondCountableTopology G] : T2Space (SchwartzBruhat G) := by sorry

/-- Paper: Lemma D.1.5.6(1), p. 763. Each structural stage inherits its intrinsic
topology from the final locally convex topology. -/
theorem schwartzBruhatStage_isEmbedding [SecondCountableTopology G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    IsEmbedding (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
      schwartzBruhatStageInclusion a e) := by sorry

/-- Paper: Lemma D.1.5.6(2), p. 763. Every bounded subset of the limit is
the image of a bounded subset of a single stage. -/
theorem schwartzBruhat_bounded_image_stage [SecondCountableTopology G]
    {B : Set (SchwartzBruhat G)} (hB : IsVonNBounded ℂ B) :
    ∃ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
      (C : Set (SchwartzBruhatStage e)), IsVonNBounded ℂ C ∧
        (show SchwartzBruhatStage e →ₗ[ℂ] SchwartzBruhat G from
          schwartzBruhatStageInclusion a e) '' C = B := by sorry

end SchwartzBruhat

section MainTheorems

universe v

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

/-- Paper: Theorem D.1.5.7, p. 763. The Schwartz–Bruhat space is barrelled. -/
theorem schwartzBruhat_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is bornological, including beyond the second-countable case.
Deviation: We use the criterion that a seminorm bounded on every bounded set is continuous. -/
theorem schwartzBruhat_bornological :
    ∀ p : Seminorm ℂ (SchwartzBruhat G),
      (∀ B : Set (SchwartzBruhat G), IsVonNBounded ℂ B → BddAbove (p '' B)) →
        Continuous p := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. The Schwartz–Bruhat space
is complete for its additive uniformity, including beyond the second-countable case. -/
theorem schwartzBruhat_complete :
    CompleteSpace (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is complete. -/
theorem schwartzBruhat_strongDual_complete [SecondCountableTopology G] :
    CompleteSpace (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The Schwartz–Bruhat space of a second-countable
group is nuclear. -/
theorem schwartzBruhat_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
of a second-countable group is nuclear. -/
theorem schwartzBruhat_strongDual_nuclear [SecondCountableTopology G] :
    IsNuclearTVS.{v} (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Closed bounded subsets
of the Schwartz–Bruhat space are compact, including beyond the second-countable case. -/
theorem schwartzBruhat_montel :
    MontelSpace ℂ (SchwartzBruhat G) := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. Closed bounded subsets of the strong dual
of the Schwartz–Bruhat space are compact. -/
theorem schwartzBruhat_strongDual_montel [SecondCountableTopology G] :
    MontelSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Theorem D.1.5.7 and Remark D.1.5.8, p. 764. Evaluation gives a
linear homeomorphism with the strong bidual, the paper's reflexivity property
of Montel spaces, including beyond the second-countable case. -/
theorem schwartzBruhat_reflexive :
    ∃ e : SchwartzBruhat G ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (SchwartzBruhat G)),
      ∀ f L, e f L = L f := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. Evaluation identifies the strong dual
linearly and topologically with its own strong bidual. -/
theorem schwartzBruhat_strongDual_reflexive [SecondCountableTopology G] :
    let D := StrongDual ℂ (SchwartzBruhat G)
    letI : TopologicalSpace D := inferInstanceAs (TopologicalSpace (StrongDual ℂ (SchwartzBruhat G)))
    let DD := StrongDual ℂ D
    letI : TopologicalSpace DD := ContinuousLinearMap.topologicalSpace
    letI : TopologicalSpace (StrongDual ℂ DD) := ContinuousLinearMap.topologicalSpace
    ∃ e : D ≃L[ℂ] StrongDual ℂ DD, ∀ L M, e L M = M L := by sorry

/-- Paper: Theorem D.1.5.7, p. 764. The strong dual of the Schwartz–Bruhat space
is barrelled. -/
theorem schwartzBruhat_strongDual_barrelled [SecondCountableTopology G] :
    BarrelledSpace ℂ (StrongDual ℂ (SchwartzBruhat G)) := by sorry

/-- Paper: Remark D.1.5.8, p. 764. The Schwartz–Bruhat space of a group that
fails second countability fails nuclearity. -/
theorem schwartzBruhat_not_nuclear (hG : ¬ SecondCountableTopology G) :
    ¬ IsNuclearTVS.{v} (SchwartzBruhat G) := by sorry

/-- Paper: Proposition D.1.5.9, p. 764. Every defining countable sequence
of Fréchet stages for the Schwartz–Bruhat space is acyclic in the sense of §C.1.5.
Deviation: A defining sequence is expressed using the compatible injections and the
locally convex limit topology of `IsInjectiveLCLimit`. -/
theorem schwartzBruhat_acyclic [SecondCountableTopology G]
    {X : ℕ → Type*} [∀ n, AddCommGroup (X n)] [∀ n, Module ℂ (X n)]
    [∀ n, TopologicalSpace (X n)] (hX : ∀ n, IsFrechetTVS (X n))
    {j : ∀ n, X n →L[ℂ] X (n + 1)} {i : ∀ n, X n →L[ℂ] SchwartzBruhat G}
    (h : IsInjectiveLCLimit j i) : IsAcyclicSystem j := by sorry

/-- Paper: Theorem D.1.5.10, p. 765. A cofinal increasing sequence of structural
stages gives a short topologically exact sequence. The difference map embeds
as the closed kernel of the quotient map given by summing the stage inclusions.
Deviation: Each stage is expressed in an elementary presentation and the difference
map uses the induced maps between successive presentations. -/
theorem schwartzBruhat_exists_topologicallyExact [SecondCountableTopology G] :
    ∃ (a : ℕ → BruhatStructuralPair G)
      (e : ∀ n, ElementaryLCAPresentation (a n).quotient)
      (j : ∀ n, SchwartzBruhatStage (e n) →L[ℂ] SchwartzBruhatStage (e (n + 1))),
      Monotone a ∧ (∀ b, ∃ n, b ≤ a n) ∧
      (∀ n f, schwartzBruhatStageRealization (a (n + 1)) (e (n + 1)) (j n f) =
        schwartzBruhatStageRealization (a n) (e n) f) ∧
      let X := fun n ↦ SchwartzBruhatStage (e n)
      let q := DirectSum.toModule ℂ ℕ (SchwartzBruhat G)
        (fun n ↦ (show X n →ₗ[ℂ] SchwartzBruhat G from schwartzBruhatStageInclusion (a n) (e n)))
      letI := locallyConvexFinalTopology (DirectSum.lof ℂ ℕ X)
      IsClosedEmbedding (directSumDifference j) ∧
        LinearMap.range (directSumDifference j) = LinearMap.ker q ∧ IsQuotientMap q := by sorry

end MainTheorems

/-! ## Deferred from §C.1 -/

section DeferredFromC1

open NumberField

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
adele ring of a number field is nonmetrizable. -/
theorem schwartzBruhat_adele_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative (AdeleRing (𝓞 F) F))) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a number field's
idele class group is nonmetrizable. -/
theorem schwartzBruhat_ideleClass_not_metrizable (F : Type*) [Field F] [NumberField F] :
    ¬ MetrizableSpace (SchwartzBruhat (IdeleClassGroup (𝓞 F) F)) := by sorry

variable (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [LocallyCompactSpace L]

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of the additive
group of a nonarchimedean local field is nonmetrizable. -/
theorem schwartzBruhat_localField_not_metrizable :
    ¬ MetrizableSpace (SchwartzBruhat (Multiplicative L)) := by sorry

/-- Paper: Remark C.1.3.3, p. 660. The Schwartz–Bruhat space of a nonarchimedean
local field has countably infinite complex dimension. -/
theorem schwartzBruhat_localField_rank :
    Module.rank ℂ (SchwartzBruhat (Multiplicative L)) = ℵ₀ := by sorry

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Paper: Example C.1.4.6(3), p. 662. The complete Schwartz–Bruhat space of a
second-countable LCA group is quasi-complete. The example's other properties
are `schwartzBruhat_complete`, `schwartzBruhat_nuclear`, `schwartzBruhat_montel`
and `schwartzBruhat_reflexive` from Theorem D.1.5.7. -/
theorem schwartzBruhat_quasiComplete :
    QuasiCompleteSpace ℂ (SchwartzBruhat G) := by sorry

end DeferredFromC1

end RiemannMasullo
