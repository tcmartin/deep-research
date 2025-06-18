import { createFireworks } from '@ai-sdk/fireworks';
import { createOpenAI } from '@ai-sdk/openai';
import {
  extractReasoningMiddleware,
  LanguageModelV1,
  wrapLanguageModel,
} from 'ai';
import { getEncoding } from 'js-tiktoken';
import { RecursiveCharacterTextSplitter } from './text-splitter';

/* ────────────────────────────────────────────────────────────────────────────
   PROVIDERS
   ────────────────────────────────────────────────────────────────────────── */

/** Standard OpenAI-hosted or Azure-style endpoint */
const openai = process.env.OPENAI_KEY
  ? createOpenAI({
      apiKey: process.env.OPENAI_KEY,
      baseURL: process.env.OPENAI_ENDPOINT || 'https://api.openai.com/v1',
    })
  : undefined;

/** Fireworks.ai provider */
const fireworks = process.env.FIREWORKS_KEY
  ? createFireworks({ apiKey: process.env.FIREWORKS_KEY })
  : undefined;

/** Ollama or any other OpenAI-compatible host (Groq, Together, etc.) */
const ollama = process.env.OLLAMA_BASE_URL
  ? createOpenAI({
      // any non-empty string placates the SDK; Ollama ignores it
      apiKey: process.env.OLLAMA_API_KEY || 'ollama-key',
      baseURL: process.env.OLLAMA_BASE_URL, // e.g. http://localhost:11434/v1
    })
  : undefined;

/* ────────────────────────────────────────────────────────────────────────────
   MODEL INSTANCES
   ────────────────────────────────────────────────────────────────────────── */

/** User-supplied env vars to force a model */
const CUSTOM_MODEL = process.env.CUSTOM_MODEL;   // for OpenAI/Fireworks
const OLLAMA_MODEL = process.env.OLLAMA_MODEL;   // e.g. qwen3:8b

/** Highest-priority: explicit Ollama model */
const ollamaModel = OLLAMA_MODEL && ollama
  ? ollama(OLLAMA_MODEL, { structuredOutputs: true })
  : undefined;

/** Next priority: any other custom model ID */
const customModel = CUSTOM_MODEL && openai
  ? openai(CUSTOM_MODEL, { structuredOutputs: true })
  : undefined;

/** Default canned choices */
const o3MiniModel = openai?.('o3-mini', {
  reasoningEffort: 'medium',
  structuredOutputs: true,
});

const deepSeekR1Model = fireworks
  ? wrapLanguageModel({
      model: fireworks(
        'accounts/fireworks/models/deepseek-r1',
      ) as LanguageModelV1,
      middleware: extractReasoningMiddleware({ tagName: 'think' }),
    })
  : undefined;

/* ────────────────────────────────────────────────────────────────────────────
   EXPORTED FACTORY
   ────────────────────────────────────────────────────────────────────────── */

export function getModel(): LanguageModelV1 {
  const model =
    // precedence order
    ollamaModel ??
    customModel ??
    deepSeekR1Model ??
    o3MiniModel;

  if (!model) {
    throw new Error('No language model is configured.  Set OPENAI_KEY, FIREWORKS_KEY, or OLLAMA_BASE_URL + OLLAMA_MODEL in .env');
  }

  return model;
}

/* ────────────────────────────────────────────────────────────────────────────
   UTILS
   ────────────────────────────────────────────────────────────────────────── */

const MinChunkSize = 140;
const encoder = getEncoding('o200k_base');

export function trimPrompt(
  prompt: string,
  contextSize = Number(process.env.CONTEXT_SIZE) || 128_000,
) {
  if (!prompt) return '';

  const length = encoder.encode(prompt).length;
  if (length <= contextSize) return prompt;

  const overflowTokens = length - contextSize;
  const chunkSize = prompt.length - overflowTokens * 3;

  if (chunkSize < MinChunkSize) return prompt.slice(0, MinChunkSize);

  const splitter = new RecursiveCharacterTextSplitter({
    chunkSize,
    chunkOverlap: 0,
  });
  const trimmed = splitter.splitText(prompt)[0] ?? '';

  return trimmed.length === prompt.length
    ? trimPrompt(prompt.slice(0, chunkSize), contextSize)
    : trimPrompt(trimmed, contextSize);
}

