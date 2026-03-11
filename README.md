# Categorical Logic

This repo aims to provide a formalization for operads (planar, symmetric, cartesian) through a generic API. There is a lot of stuff about profunctors and related topics in here.

The original aim was to use operads to give a fully general definition for terms and their different flavours. Mainly, full terms as used in first-order logic, terms as in linear logic, where you can't use variables twice (no diagonal), and a symmetric variation of those.

The API allows one can then prove and state simple results about deduction (and computation thereof), completeness and soundness about these different term models all at once. This is WIP, since the foundations are not there yet.